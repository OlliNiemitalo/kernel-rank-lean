"""
GPU implementations shared by blur_2d.py and acoustics_3d.py: separable FIR cascades, direct stencils,
and cuFFT plans, each validated against float64 references by the calling benchmarks.

Three techniques make the separable cascades fast on a GPU whose DRAM bandwidth (hundreds of GB/s) is far
below its L2-cache and arithmetic throughput:

  1. Register sliding windows. A program computes K consecutive outputs along the filtered axis and keeps
     the K rows needed on each side of the symmetric FIR in registers, so each tap costs one new row load
     per side for K outputs. The tap loop is unrolled K times with rotating slot roles, so no register
     moves are needed; the L mod K remaining taps are unrolled after the loop.
  2. All terms per pass. The first pass loads each input row once and updates all R terms (fan-out); the
     last pass sums all R terms (fan-in). No per-term launches or accumulator read-modify-write passes.
  3. Cache-resident intermediates. The image or volume is processed in strips (2-D) or slabs (3-D) whose
     R intermediate channels fit in the L2 cache, so only the input and the output cross DRAM.

A FIR is only windowed along an axis that is strided in memory (the tensor axis must stay contiguous for
coalesced loads). The 2-D blur therefore stores its strip intermediates transposed, and the 3-D step
filters the contiguous z axis last, with each thread owning a short run of z values.

Kernels whose structure depends on K, R or L are generated as source text and compiled by Triton.
"""
import linecache
import math

import numpy as np
import torch
import triton
import triton.language as tl

L2_BUDGET_BYTES = 16 << 20


def cuda_batch_stats(fn, warmup: int = 8, n_batches: int = 10, iters_per_batch: int = 15):
    """Mean and standard deviation (ms per call) over CUDA-Event-timed batches of `fn`."""
    for _ in range(warmup):
        fn()
    torch.cuda.synchronize()
    batch_ms = []
    for _ in range(n_batches):
        s_ev = torch.cuda.Event(enable_timing=True)
        e_ev = torch.cuda.Event(enable_timing=True)
        s_ev.record()
        for _ in range(iters_per_batch):
            fn()
        e_ev.record()
        torch.cuda.synchronize()
        batch_ms.append(s_ev.elapsed_time(e_ev) / iters_per_batch)
    arr = np.array(batch_ms, dtype=np.float64)
    return float(np.mean(arr)), float(np.std(arr, ddof=1))


def max_rms_error(out: torch.Tensor, ref64: torch.Tensor):
    """Maximum and root-mean-square absolute error of `out` against a float64 reference."""
    d = (out.to(torch.float64) - ref64).abs()
    return float(d.max()), float(torch.sqrt((d * d).mean()))


def fastest(configs, make, run, warmup: int = 2, n_batches: int = 3, iters_per_batch: int = 8):
    """Build a plan for each config, time `run(plan)`, and return (plan, config, ms) of the fastest."""
    best = None
    for cfg in configs:
        plan = make(cfg)
        ms, _ = cuda_batch_stats(lambda: run(plan), warmup, n_batches, iters_per_batch)
        if best is None or ms < best[2]:
            best = (plan, cfg, ms)
    return best


def window_sizes(k_max: int):
    """Candidate window sizes: the largest that fits the register budget, three quarters and half of it."""
    return sorted({max(k, 2) for k in (k_max, 3 * k_max // 4, k_max // 2)}, reverse=True)


class Launcher:
    """
    Launches a Triton kernel through its cached compiled handle, which skips the per-call argument
    specialization (about 10 us -> 6 us per launch). Integer arguments that vary between calls must be
    listed in the kernel's `do_not_specialize`.
    """

    def __init__(self, fn, num_warps: int = 4, **constexprs):
        self.fn, self.num_warps, self.constexprs, self.compiled = fn, num_warps, constexprs, None

    def __call__(self, grid, *args):
        if self.compiled is None:
            self.compiled = self.fn[grid](*args, num_warps=self.num_warps, **self.constexprs)
            self.tail = tuple(self.constexprs[n] for n in self.fn.arg_names[len(args):])
        else:
            self.compiled[grid](*args, *self.tail)


_generated = {}


def _generate(name: str, lines):
    """Compile generated Triton source once per name; `linecache` makes the source visible to `inspect`."""
    if name not in _generated:
        src = "\n".join(lines) + "\n"
        fname = f"<generated {name}>"
        linecache.cache[fname] = (len(src), None, src.splitlines(True), fname)
        scope = {"triton": triton, "tl": tl}
        exec(compile(src, fname, "exec"), scope)
        _generated[name] = scope[name]
    return _generated[name]


def _fanout_tap(o, K: int, R: int, t: int, row_ptr, indent: str):
    o.append(f"{indent}p{(t - 1) % K} = {row_ptr(f'r0 + {K - 1 + t} + m0')}")
    o.append(f"{indent}q{(-t) % K} = {row_ptr(f'r0 - {t} - m0')}")
    for i in range(K):
        o.append(f"{indent}s{i} = p{(i + t) % K} + q{(i - t) % K}")
    for n in range(R):
        o.append(f"{indent}w = tl.load(w_ptr + (m0 + {t}) * {R} + {n})")
        for i in range(K):
            o.append(f"{indent}a{n}_{i} += w * s{i}")


def _window_fanout(o, K: int, R: int, rem: int, row_ptr, indent: str = "    "):
    """
    Emit the rotating K-row window of a symmetric FIR with L = K * nb + rem taps per side for R terms.
    `row_ptr(expr)` gives the source of the load of row `expr` (already border-mapped). Row `r0 + j` lives
    in slot `j mod K`; at tap m = m0 + t the plus side replaces slot (t - 1) mod K, the minus side slot
    (-t) mod K, and output i uses slots (i + t) mod K and (i - t) mod K. Weights are w[m * R + n];
    accumulators are a{n}_{i}.
    """
    for i in range(K):
        o.append(f"{indent}p{i} = {row_ptr(f'r0 + {i}')}")
        o.append(f"{indent}q{i} = p{i}")
    for n in range(R):
        o.append(f"{indent}w = tl.load(w_ptr + {n})")
        for i in range(K):
            o.append(f"{indent}a{n}_{i} = w * p{i}")
    o.append(f"{indent}for b in range(nb):")
    o.append(f"{indent}    m0 = b * {K}")
    for t in range(1, K + 1):
        _fanout_tap(o, K, R, t, row_ptr, indent + "    ")
    if rem:
        o.append(f"{indent}m0 = nb * {K}")
        for t in range(1, rem + 1):
            _fanout_tap(o, K, R, t, row_ptr, indent)


def _single_tap(o, K: int, t: int, row_ptr, indent: str):
    o.append(f"{indent}p{(t - 1) % K} = {row_ptr(f'r0 + {K - 1 + t} + m0')}")
    o.append(f"{indent}q{(-t) % K} = {row_ptr(f'r0 - {t} - m0')}")
    o.append(f"{indent}w = tl.load(wp + m0 + {t})")
    for i in range(K):
        o.append(f"{indent}a{i} += w * (p{(i + t) % K} + q{(i - t) % K})")


def _window_single(o, K: int, rem: int, row_ptr, indent: str):
    """Rotating K-row window for one term with weights wp[m]; accumulators a{i} must already exist."""
    o.append(f"{indent}w = tl.load(wp)")
    for i in range(K):
        o.append(f"{indent}p{i} = {row_ptr(f'r0 + {i}')}")
        o.append(f"{indent}q{i} = p{i}")
        o.append(f"{indent}a{i} += w * p{i}")
    o.append(f"{indent}for b in range(nb):")
    o.append(f"{indent}    m0 = b * {K}")
    for t in range(1, K + 1):
        _single_tap(o, K, t, row_ptr, indent + "    ")
    if rem:
        o.append(f"{indent}m0 = nb * {K}")
        for t in range(1, rem + 1):
            _single_tap(o, K, t, row_ptr, indent)


def _f32(a: np.ndarray) -> torch.Tensor:
    return torch.tensor(np.ascontiguousarray(a), dtype=torch.float32, device="cuda")


# ----------------------------------------------------------------------------------------------------
# 2-D blur: clamped (replicate) borders, row-major interleaved image img[y, x, c]
# ----------------------------------------------------------------------------------------------------

def _clamp(v: str, n: str) -> str:
    return f"tl.minimum(tl.maximum({v}, 0), {n} - 1)"


def blur_rows_fanout_kernel(K: int, R: int, rem: int):
    """Vertical FIR of img[y, x, c] into R transposed strip planes mid[n, x, y - ys0, c]; w[m * R + n]."""
    name = f"blur_rows_fanout_k{K}_r{R}_m{rem}"
    o = ["@triton.jit(do_not_specialize=['ys0'])",
         f"def {name}(inp_ptr, mid_ptr, w_ptr, nb, ys0, S, "
         "H: tl.constexpr, W: tl.constexpr, C: tl.constexpr, BLOCK: tl.constexpr):",
         f"    r0 = ys0 + tl.program_id(0) * {K}",
         "    offs = tl.program_id(1) * BLOCK + tl.arange(0, BLOCK)",
         "    src = inp_ptr + offs"]
    _window_fanout(o, K, R, rem, lambda r: f"tl.load(src + {_clamp(r, 'H')} * (W * C)).to(tl.float32)")
    o += ["    ty = mid_ptr.dtype.element_ty",
          "    dst = mid_ptr + (offs // C) * (S * C) + (offs % C) + (r0 - ys0) * C"]
    for n in range(R):
        for i in range(K):
            o.append(f"    tl.store(dst + {n} * (W * S * C) + {i} * C, a{n}_{i}.to(ty))")
    return _generate(name, o)


def blur_cols_fanin_kernel(K: int, rem: int):
    """Horizontal FIR of R transposed strip planes mid[n, x, s, c], summed into img[ys0 + s, x, c]; w[n, m]."""
    name = f"blur_cols_fanin_k{K}_m{rem}"
    o = ["@triton.jit(do_not_specialize=['ys0'])",
         f"def {name}(mid_ptr, out_ptr, w_ptr, nb, ys0, S, "
         "H: tl.constexpr, W: tl.constexpr, C: tl.constexpr, R: tl.constexpr, BLOCK: tl.constexpr):",
         f"    r0 = tl.program_id(0) * {K}",
         "    offs = tl.program_id(1) * BLOCK + tl.arange(0, BLOCK)"]
    for i in range(K):
        o.append(f"    a{i} = tl.zeros([BLOCK], dtype=tl.float32)")
    o += ["    for n in range(R):",
          "        src = mid_ptr + n * (W * S * C) + offs",
          f"        wp = w_ptr + n * ({K} * nb + {rem + 1})"]
    _window_single(o, K, rem, lambda r: f"tl.load(src + {_clamp(r, 'W')} * (S * C)).to(tl.float32)", "        ")
    o += ["    ty = out_ptr.dtype.element_ty",
          "    y = ys0 + offs // C",
          "    mask = y < H",
          "    dst = out_ptr + y * (W * C) + (offs % C) + r0 * C"]
    for i in range(K):
        o.append(f"    if r0 + {i} < W:")
        o.append(f"        tl.store(dst + {i} * C, a{i}.to(ty), mask=mask)")
    return _generate(name, o)


class SeparableBlur2D:
    """
    out = sum_n (h_n along x) (v_n along y) * inp for even stencils given as half arrays Hh, Vh of shape
    (R, L + 1), with clamped borders. `inp` and `out` are (H, W, C) tensors of one dtype (float32 or
    float16); the strip intermediates use the same dtype and accumulation is in float32.
    """

    def __init__(self, Hh, Vh, H: int, W: int, C: int, dtype, k_rows: int, k_cols: int,
                 block_rows: int = 32, warps_rows: int = 1, block_cols: int = 32, warps_cols: int = 1,
                 strip_bytes: int = L2_BUDGET_BYTES):
        R, L = Hh.shape[0], Hh.shape[1] - 1
        self.H, self.W, self.C, self.R = H, W, C, R
        self.k_rows, self.k_cols, self.block_rows, self.block_cols = k_rows, k_cols, block_rows, block_cols
        assert (W * C) % block_rows == 0 and block_cols % C == 0
        unit = math.lcm(k_rows, block_cols // C)
        row_bytes = R * W * C * torch.empty((), dtype=dtype).element_size()
        self.S = unit * max(1, round(strip_bytes / (row_bytes * unit)))
        self.nb_rows, self.nb_cols = L // k_rows, L // k_cols
        self.w_rows, self.w_cols = _f32(Vh.T), _f32(Hh)
        self.mid = torch.empty((R, W, self.S, C), device="cuda", dtype=dtype)
        self.rows_pass = Launcher(blur_rows_fanout_kernel(k_rows, R, L % k_rows), warps_rows, H=H, W=W, C=C, BLOCK=block_rows)
        self.cols_pass = Launcher(blur_cols_fanin_kernel(k_cols, L % k_cols), warps_cols, H=H, W=W, C=C, R=R, BLOCK=block_cols)
        self.config = {"k_rows": k_rows, "k_cols": k_cols, "block_rows": block_rows, "warps_rows": warps_rows,
                       "block_cols": block_cols, "warps_cols": warps_cols, "strip_rows": self.S}

    def rows(self, inp, ys0: int, n_rows: int):
        grid = (-(-n_rows // self.k_rows), (self.W * self.C) // self.block_rows, 1)
        self.rows_pass(grid, inp, self.mid, self.w_rows, self.nb_rows, ys0, self.S)

    def cols(self, out, ys0: int, n_rows: int):
        grid = (-(-self.W // self.k_cols), -(-(n_rows * self.C) // self.block_cols), 1)
        self.cols_pass(grid, self.mid, out, self.w_cols, self.nb_cols, ys0, self.S)

    def __call__(self, inp, out):
        for ys0 in range(0, self.H, self.S):
            n_rows = min(self.S, self.H - ys0)
            self.rows(inp, ys0, n_rows)
            self.cols(out, ys0, n_rows)

    @classmethod
    def tuned(cls, Hh, Vh, inp, out):
        """Pick window sizes, block shapes and strip size by timing each pass, then the whole blur."""
        H, W, C = inp.shape
        R = Hh.shape[0]
        shapes = [(32, 1), (64, 1)]  # (block, warps): 1 or 2 elements per thread

        def strips(plan, fn):
            for ys0 in range(0, H, plan.S):
                fn(ys0, min(plan.S, H - ys0))

        row_cfgs = [(k, b, w) for b, w in shapes for k in window_sizes(min(12, 96 // (R * b // (32 * w))))]
        k_cols0 = 16
        _, (k_rows, block_rows, warps_rows), _ = fastest(
            row_cfgs, lambda c: cls(Hh, Vh, H, W, C, inp.dtype, c[0], k_cols0, c[1], c[2]),
            lambda p: strips(p, lambda ys0, n: p.rows(inp, ys0, n)))
        col_cfgs = [(k, b, w) for b, w in shapes for k in window_sizes(32 // (b // (32 * w)))]
        _, (k_cols, block_cols, warps_cols), _ = fastest(
            col_cfgs, lambda c: cls(Hh, Vh, H, W, C, inp.dtype, k_rows, c[0], block_rows, warps_rows, c[1], c[2]),
            lambda p: strips(p, lambda ys0, n: p.cols(out, ys0, n)))
        plan, _, _ = fastest(
            [L2_BUDGET_BYTES // 2, L2_BUDGET_BYTES, 3 * L2_BUDGET_BYTES // 2],
            lambda sb: cls(Hh, Vh, H, W, C, inp.dtype, k_rows, k_cols, block_rows, warps_rows, block_cols, warps_cols, sb),
            lambda p: p(inp, out), warmup=3, n_batches=3, iters_per_batch=6)
        return plan


def blur_direct_kernel(K: int):
    """
    Direct (2L+1) x (2L+1) convolution of img[y, x, c] with clamped borders, K output rows per program:
    each loaded row segment feeds all K rows. k_ptr is the kernel zero-padded by K - 1 rows on both sides.
    """
    o = ["@triton.jit",
         f"def blur_direct_k{K}(inp_ptr, out_ptr, k_ptr, L, H: tl.constexpr, W: tl.constexpr, C: tl.constexpr, BLOCK: tl.constexpr):",
         f"    y0 = tl.program_id(0) * {K}",
         "    blk = tl.program_id(1)",
         "    offs = blk * BLOCK + tl.arange(0, BLOCK)",
         "    ROW = W * C",
         "    Wt = 2 * L + 1",
         "    mask = offs < ROW",
         "    x = offs // C",
         "    c = offs % C",
         "    interior = (blk * BLOCK >= L * C) and ((blk + 1) * BLOCK + L * C <= ROW)"]
    for i in range(K):
        o.append(f"    a{i} = tl.zeros([BLOCK], dtype=tl.float32)")
    o += [f"    for rr in range(0, Wt + {K - 1}):",
          f"        row = inp_ptr + {_clamp('y0 - L + rr', 'H')} * ROW",
          "        kp = k_ptr + rr * Wt + L"]
    for interior in (True, False):
        o.append("        if interior:" if interior else "        else:")
        o.append("            for dx in range(-L, L + 1):")
        if interior:
            o.append("                v = tl.load(row + offs + dx * C).to(tl.float32)")
        else:
            o.append(f"                v = tl.load(row + {_clamp('x + dx', 'W')} * C + c, mask=mask, other=0.0).to(tl.float32)")
        for i in range(K):
            o.append(f"                a{i} += tl.load(kp + {K - 1 - i} * Wt + dx) * v")
    o.append("    ty = out_ptr.dtype.element_ty")
    for i in range(K):
        o.append(f"    if y0 + {i} < H:")
        o.append(f"        tl.store(out_ptr + (y0 + {i}) * ROW + offs, a{i}.to(ty), mask=mask)")
    return _generate(f"blur_direct_k{K}", o)


class DirectBlur2D:
    """out = K2 * inp for a dense (2L+1) x (2L+1) kernel with clamped borders; (H, W, C) tensors."""

    CONFIGS = [(4, 256, 1), (4, 512, 2), (8, 512, 2)]  # (rows per program, block, warps)

    def __init__(self, K2: np.ndarray, H: int, W: int, C: int, k_rows: int = 4, block: int = 256, warps: int = 1):
        Wt = K2.shape[0]
        self.L, self.H, self.W, self.C, self.k_rows, self.block = Wt // 2, H, W, C, k_rows, block
        kpad = np.zeros((Wt + 2 * (k_rows - 1), Wt))
        kpad[k_rows - 1: k_rows - 1 + Wt] = K2
        self.kpad = _f32(kpad)
        self.launch = Launcher(blur_direct_kernel(k_rows), warps, H=H, W=W, C=C, BLOCK=block)
        self.config = {"k_rows": k_rows, "block": block, "warps": warps}

    def __call__(self, inp, out):
        grid = (-(-self.H // self.k_rows), -(-(self.W * self.C) // self.block), 1)
        self.launch(grid, inp, out, self.kpad, self.L)

    @classmethod
    def tuned(cls, K2, inp, out):
        H, W, C = inp.shape
        return fastest(cls.CONFIGS, lambda c: cls(K2, H, W, C, *c), lambda p: p(inp, out), 1, 2, 2)[0]


@triton.jit
def pad_pairs_kernel(inp_ptr, buf_ptr, H: tl.constexpr, W: tl.constexpr, Hc: tl.constexpr, Wc: tl.constexpr,
                     L: tl.constexpr, CLAMP: tl.constexpr, BLOCK: tl.constexpr):
    """
    Copy inp[p, y, x, q] (p, q < 2) into the periodic buffer buf[p, y', x', q] of size Hc x Wc.
    CLAMP: replicate-pad by L on every side, with the left/top padding wrapped to the far end.
    Otherwise copy to the top-left corner (the rest of the buffer stays zero).
    """
    yc = tl.program_id(0)
    p = tl.program_id(1)
    offs = tl.program_id(2) * BLOCK + tl.arange(0, BLOCK)
    xs = offs // 2
    q = offs % 2
    if CLAMP:
        mask = xs < Wc
        ys = tl.where(yc < H + L, yc, yc - Hc)
        ys = tl.minimum(tl.maximum(ys, 0), H - 1)
        xx = tl.where(xs < W + L, xs, xs - Wc)
        xx = tl.minimum(tl.maximum(xx, 0), W - 1)
        v = tl.load(inp_ptr + ((p * H + ys) * W + xx) * 2 + q, mask=mask, other=0.0)
        tl.store(buf_ptr + ((p * Hc + yc) * Wc + xs) * 2 + q, v, mask=mask)
    else:
        mask = xs < W
        v = tl.load(inp_ptr + (p * H + yc) * W * 2 + offs, mask=mask, other=0.0)
        tl.store(buf_ptr + (p * Hc + yc) * Wc * 2 + offs, v, mask=mask)


def smooth_sizes(lo: int, count: int, primes=(2, 3, 5, 7)):
    """The `count` smallest integers >= lo whose prime factors all lie in `primes` (fast cuFFT sizes)."""
    out = []
    n = lo
    while len(out) < count:
        m = n
        for p in primes:
            while m % p == 0:
                m //= p
        if m == 1:
            out.append(n)
        n += 1
    return out


class FFTBlur2D:
    """
    Circular convolution with an even (2L+1) x (2L+1) kernel by cuFFT. A four-channel image is stored as
    two complex planes inp[p, y, x, :] = (re, im) (channels 2p and 2p + 1): because the kernel is real, one
    complex-to-complex transform filters both channels, and it runs in place. The kernel is centered at the
    origin, so its spectrum is real and no output shift is needed; the 1/n normalization is folded into it.

    mode "zero": zero padding, period >= size + L.  mode "clamp": replicate padding, period >= size + 2L.
    Returns a (2, H, W, 2) float32 view of the result buffer.
    """

    def __init__(self, K2: np.ndarray, H: int, W: int, mode: str, Hc: int, Wc: int, per_plane: bool = False):
        self.H, self.W, self.Hc, self.Wc, self.clamp, self.per_plane = H, W, Hc, Wc, mode == "clamp", per_plane
        self.L = L = K2.shape[0] // 2
        assert Hc >= H + (2 if self.clamp else 1) * L and Wc >= W + (2 if self.clamp else 1) * L
        k = torch.zeros((Hc, Wc), dtype=torch.float64, device="cuda")
        idx = torch.arange(-L, L + 1, device="cuda")
        k[(idx % Hc)[:, None], (idx % Wc)[None, :]] = torch.tensor(K2, device="cuda")
        spec = torch.fft.fft2(k)
        assert float(spec.imag.abs().max()) <= 1e-9 * float(spec.real.abs().max()), "kernel must be even"
        self.khat = (spec.real / (Hc * Wc)).to(torch.float32).contiguous()
        self.buf = torch.zeros((2, Hc, Wc, 2), device="cuda", dtype=torch.float32)
        self.zbuf = torch.view_as_complex(self.buf)
        self.res = torch.empty((2, Hc, Wc), device="cuda", dtype=torch.complex64)
        self.config = {"fft_shape": [Hc, Wc], "per_plane": per_plane}

    def __call__(self, inp):
        rows, cols = (self.Hc, self.Wc) if self.clamp else (self.H, self.W)
        pad_pairs_kernel[(rows, 2, triton.cdiv(2 * cols, 1024))](
            inp, self.buf, H=self.H, W=self.W, Hc=self.Hc, Wc=self.Wc, L=self.L, CLAMP=self.clamp, BLOCK=1024)
        if self.per_plane:
            for p in range(2):
                spec = torch.fft.fft2(self.zbuf[p])
                spec.mul_(self.khat)
                torch.fft.ifft2(spec, norm="forward", out=self.res[p])
            res = self.res
        else:
            spec = torch.fft.fft2(self.zbuf)
            spec.mul_(self.khat)
            res = torch.fft.ifft2(spec, norm="forward")
        return torch.view_as_real(res)[:, : self.H, : self.W]

    @classmethod
    def tuned(cls, K2, inp, mode: str, n_sizes: int = 5):
        """Time the smallest 7-smooth periods in each dimension and both batching variants."""
        _, H, W, _ = inp.shape
        pad = (2 if mode == "clamp" else 1) * (K2.shape[0] // 2)
        sizes = [(hc, wc) for hc in smooth_sizes(H + pad, n_sizes) for wc in smooth_sizes(W + pad, n_sizes)]
        _, (Hc, Wc), _ = fastest(sizes, lambda s: cls(K2, H, W, mode, *s), lambda p: p(inp), 2, 2, 6)
        return fastest([False, True], lambda v: cls(K2, H, W, mode, Hc, Wc, v), lambda p: p(inp), 3, 3, 8)[0]


# ----------------------------------------------------------------------------------------------------
# 3-D leapfrog steps: half-sample (Neumann) reflection, fields p[x, y, z] on a G^3 grid
# ----------------------------------------------------------------------------------------------------

def _reflect(v: str) -> str:
    """Half-sample symmetric index map: -1 -> 0 and G -> G - 1 (valid for -G <= v < 2G)."""
    return f"tl.where({v} < 0, -1 - ({v}), tl.where({v} >= G, 2 * G - 1 - ({v}), {v}))"


def step_x_fanout_kernel(K: int, R: int, rem: int):
    """x FIR of p[x, y, z] into R slab planes mid[n, x - xs0, y, z]; w[m * R + n]."""
    name = f"step_x_fanout_k{K}_r{R}_m{rem}"
    o = ["@triton.jit(do_not_specialize=['xs0', 'SX'])",
         f"def {name}(p_ptr, mid_ptr, w_ptr, nb, xs0, SX, G: tl.constexpr, BLOCK: tl.constexpr):",
         f"    r0 = xs0 + tl.program_id(0) * {K}",
         "    offs = tl.program_id(1) * BLOCK + tl.arange(0, BLOCK)",
         "    src = p_ptr + offs"]

    def row(r):
        return f"tl.load(src + {_reflect('(' + r + ')')} * (G * G)).to(tl.float32)"

    _window_fanout(o, K, R, rem, row)
    o += ["    ty = mid_ptr.dtype.element_ty",
          "    dst = mid_ptr + (r0 - xs0) * (G * G) + offs"]
    for n in range(R):
        for i in range(K):
            o.append(f"    tl.store(dst + ({n} * SX + {i}) * (G * G), a{n}_{i}.to(ty))")
    return _generate(name, o)


def step_y_map_kernel(K: int, rem: int):
    """y FIR of each slab plane mid1[n, xs, y, z] into mid2[n, xs, y, z], with per-term weights w[n, m]."""
    name = f"step_y_map_k{K}_m{rem}"
    o = ["@triton.jit(do_not_specialize=['nx', 'SX'])",
         f"def {name}(m1_ptr, m2_ptr, w_ptr, nb, nx, SX, G: tl.constexpr, BLOCK: tl.constexpr):",
         f"    r0 = tl.program_id(0) * {K}",
         "    plane = tl.program_id(1)",
         "    n = plane // nx",
         "    base = (n * SX + plane % nx) * (G * G) + tl.program_id(2) * BLOCK + tl.arange(0, BLOCK)",
         "    src = m1_ptr + base",
         f"    wp = w_ptr + n * ({K} * nb + {rem + 1})"]
    for i in range(K):
        o.append(f"    a{i} = tl.zeros([BLOCK], dtype=tl.float32)")
    _window_single(o, K, rem, lambda r: f"tl.load(src + {_reflect('(' + r + ')')} * G).to(tl.float32)", "    ")
    o.append("    ty = m2_ptr.dtype.element_ty")
    for i in range(K):
        o.append(f"    if r0 + {i} < G:")
        o.append(f"        tl.store(m2_ptr + base + (r0 + {i}) * G, a{i}.to(ty))")
    return _generate(name, o)


def step_z_fanin_kernel(E: int, L: int):
    """
    z FIR of R slab planes mid2[n, xs, y, z] and the leapfrog update
    p_next = alpha0 p_curr + sum_n fir_z(mid2_n) - p_prev.
    z is the contiguous axis, so each thread owns E consecutive z values and loads its E + 2L inputs
    once per term; weights are w[n * (L + 1) + m].
    """
    o = ["@triton.jit(do_not_specialize=['xs0', 'SX'])",
         f"def step_z_fanin_e{E}_l{L}(m2_ptr, pc_ptr, pp_ptr, pn_ptr, w_ptr, alpha0, xs0, SX, "
         "G: tl.constexpr, R: tl.constexpr, NT: tl.constexpr):",
         "    xs = tl.program_id(0)",
         "    y = tl.program_id(1)",
         "    zb = tl.program_id(2)",
         f"    z0 = (zb * NT + tl.arange(0, NT)) * {E}",
         f"    interior = (zb * NT * {E} >= {L}) and ((zb + 1) * NT * {E} + {L} <= G)"]
    for e in range(E):
        o.append(f"    a{e} = tl.zeros([NT], dtype=tl.float32)")
    o += ["    for n in range(R):",
          "        base = m2_ptr + ((n * SX + xs) * G + y) * G",
          f"        wp = w_ptr + n * {L + 1}"]
    for m in range(L + 1):
        o.append(f"        w{m} = tl.load(wp + {m})")
    o.append("        if interior:")
    for d in range(-L, E + L):
        o.append(f"            t{d + L} = tl.load(base + z0 + {d}).to(tl.float32)")
    o.append("        else:")
    for d in range(-L, E + L):
        o.append(f"            t{d + L} = tl.load(base + {_reflect(f'(z0 + {d})')}).to(tl.float32)")
    for e in range(E):
        terms = [f"w0 * t{e + L}"] + [f"w{m} * (t{e + L + m} + t{e + L - m})" for m in range(1, L + 1)]
        o.append(f"        a{e} += " + " + ".join(terms))
    o.append("    g = ((xs0 + xs) * G + y) * G + z0")
    for e in range(E):
        o.append(f"    tl.store(pn_ptr + g + {e}, alpha0 * tl.load(pc_ptr + g + {e}) + a{e} - tl.load(pp_ptr + g + {e}))")
    return _generate(f"step_z_fanin_e{E}_l{L}", o)


class SeparableStep3D:
    """
    Leapfrog step p_next = alpha0 p_curr + sum_n (fx_n (x) fy_n (x) fz_n) * p_curr - p_prev for even
    half-stencil triples `factors` = [(fx, fy, fz), ...] with half-sample reflecting walls. Fields are
    float32 (G, G, G) tensors; `mid_dtype` is the storage type of the two slab intermediates.
    """

    def __init__(self, factors, alpha0: float, G: int, mid_dtype=torch.float32, window: int = 4, run: int = 4,
                 slab_planes: int = 0):
        R, L = len(factors), len(factors[0][0]) - 1
        K = window
        self.G, self.R, self.K, self.E, self.alpha0 = G, R, K, run, float(alpha0)
        if slab_planes == 0:
            plane_bytes = 2 * R * G * G * torch.empty((), dtype=mid_dtype).element_size()
            slab_planes = K * max(1, int(1.25 * L2_BUDGET_BYTES / plane_bytes) // K)
        self.SX = min(slab_planes, K * -(-G // K))
        assert self.SX % K == 0
        self.nb = L // K
        self.wx = _f32(np.stack([f[0] for f in factors]).T)
        self.wy = _f32(np.stack([f[1] for f in factors]))
        self.wz = _f32(np.stack([f[2] for f in factors]))
        self.mid1 = torch.empty((R, self.SX, G, G), device="cuda", dtype=mid_dtype)
        self.mid2 = torch.empty((R, self.SX, G, G), device="cuda", dtype=mid_dtype)
        self.NT = 32 if G % (32 * run) == 0 else G // run
        self.BY = min(64, G)
        assert (G * G) % 128 == 0 and G % self.BY == 0 and G % (self.NT * run) == 0
        self.x_pass = Launcher(step_x_fanout_kernel(K, R, L % K), 4, G=G, BLOCK=128)
        self.y_pass = Launcher(step_y_map_kernel(K, L % K), 2, G=G, BLOCK=self.BY)
        self.z_pass = Launcher(step_z_fanin_kernel(run, L), 1, G=G, R=R, NT=self.NT)
        self.config = {"window": K, "run": run, "slab_planes": self.SX}

    def __call__(self, p_curr, p_prev, p_next):
        G, SX, K, R = self.G, self.SX, self.K, self.R
        for xs0 in range(0, G, SX):
            nx = min(SX, G - xs0)
            self.x_pass((-(-nx // K), (G * G) // 128, 1), p_curr, self.mid1, self.wx, self.nb, xs0, SX)
            self.y_pass((-(-G // K), R * nx, G // self.BY), self.mid1, self.mid2, self.wy, self.nb, nx, SX)
            self.z_pass((nx, G, G // (self.NT * self.E)), self.mid2, p_curr, p_prev, p_next, self.wz, self.alpha0, xs0, SX)

    @classmethod
    def tuned(cls, factors, alpha0, p_curr, p_prev, p_next, mid_dtype=torch.float32):
        """Pick the window size, z-run length and slab thickness by timing whole steps."""
        G = p_curr.shape[0]
        cfgs = [(k, e, k * j) for k in (4, 8) for e in (4, 8) for j in (1, 2, 4) if k * j <= 16]
        return fastest(cfgs, lambda c: cls(factors, alpha0, G, mid_dtype, *c),
                       lambda p: p(p_curr, p_prev, p_next), 3, 4, 10)[0]


@triton.jit
def pad_z_kernel(p_ptr, buf_ptr, G: tl.constexpr, L: tl.constexpr, BLOCK: tl.constexpr):
    """buf[x, y, z'] = p[x, y, reflect(z' - L)] for z' in [0, G + 2L)."""
    row = tl.program_id(0)
    zz = tl.program_id(1) * BLOCK + tl.arange(0, BLOCK)
    mask = zz < G + 2 * L
    zs = zz - L
    zs = tl.where(zs < 0, -1 - zs, tl.where(zs >= G, 2 * G - 1 - zs, zs))
    tl.store(buf_ptr + row * (G + 2 * L) + zz, tl.load(p_ptr + row * G + zs, mask=mask, other=0.0), mask=mask)


def step_direct_kernel(K: int):
    """
    Direct (2L+1)^3 leapfrog step p_next = stencil * p_curr - p_prev on a z-padded copy buf[x, y, z + L]
    of p_curr, K output x-planes per program. k_ptr is the stencil zero-padded by K - 1 planes in x.
    """
    o = ["@triton.jit",
         f"def step_direct_k{K}(buf_ptr, pp_ptr, pn_ptr, k_ptr, L, G: tl.constexpr, BLOCK: tl.constexpr):",
         f"    x0 = tl.program_id(0) * {K}",
         "    y = tl.program_id(1)",
         "    z = tl.program_id(2) * BLOCK + tl.arange(0, BLOCK)",
         "    Wt = 2 * L + 1"]
    for i in range(K):
        o.append(f"    a{i} = tl.zeros([BLOCK], dtype=tl.float32)")
    o += [f"    for rr in range(0, Wt + {K - 1}):",
          f"        xr = {_reflect('(x0 - L + rr)')}",
          "        for dy in range(-L, L + 1):",
          f"            row = buf_ptr + (xr * G + {_reflect('(y + dy)')}) * (G + 2 * L) + z",
          "            kp = k_ptr + (rr * Wt + dy + L) * Wt",
          "            for dz in range(0, Wt):",
          "                v = tl.load(row + dz)"]
    for i in range(K):
        o.append(f"                a{i} += tl.load(kp + {K - 1 - i} * Wt * Wt + dz) * v")
    for i in range(K):
        o.append(f"    if x0 + {i} < G:")
        o.append(f"        g = ((x0 + {i}) * G + y) * G + z")
        o.append(f"        tl.store(pn_ptr + g, a{i} - tl.load(pp_ptr + g))")
    return _generate(f"step_direct_k{K}", o)


class DirectStep3D:
    """Leapfrog step with a dense (2L+1)^3 stencil (center tap includes alpha0) and reflecting walls."""

    CONFIGS = [(4, 128, 1), (4, 256, 2), (2, 256, 1)]  # (planes per program, block, warps)

    def __init__(self, stencil: np.ndarray, G: int, k_planes: int = 4, block: int = 128, warps: int = 1):
        Wt = stencil.shape[0]
        self.G, self.L, self.k_planes, self.block = G, Wt // 2, k_planes, block
        kpad = np.zeros((Wt + 2 * (k_planes - 1), Wt, Wt))
        kpad[k_planes - 1: k_planes - 1 + Wt] = stencil
        self.kpad = _f32(kpad)
        self.buf = torch.empty((G, G, G + 2 * self.L), device="cuda", dtype=torch.float32)
        self.launch = Launcher(step_direct_kernel(k_planes), warps, G=G, BLOCK=block)
        self.config = {"k_planes": k_planes, "block": block, "warps": warps}

    def __call__(self, p_curr, p_prev, p_next):
        G, L = self.G, self.L
        pad_z_kernel[(G * G, triton.cdiv(G + 2 * L, 512))](p_curr, self.buf, G=G, L=L, BLOCK=512)
        self.launch((-(-G // self.k_planes), G, G // self.block), self.buf, p_prev, p_next, self.kpad, L)

    @classmethod
    def tuned(cls, stencil, p_curr, p_prev, p_next):
        G = p_curr.shape[0]
        return fastest(cls.CONFIGS, lambda c: cls(stencil, G, *c), lambda p: p(p_curr, p_prev, p_next), 1, 2, 2)[0]


class KSpaceStep3D:
    """
    Periodic pseudospectral leapfrog step p_next = irfftn(m_hat rfftn(p_curr)) - p_prev, with m_hat of
    shape (G, G, G // 2 + 1). The 3-D transform is split so that every stage works on an L2-resident
    chunk: 2-D real transforms over (y, z) for groups of x-planes, then, for groups of y-rows, the x
    transform, the spectral multiply and the inverse x transform, then inverse 2-D transforms fused with
    the subtraction of p_prev.
    """

    CONFIGS = [(32, 32), (32, 16), (64, 32), (16, 32)]  # (x-planes, y-rows) per chunk

    def __init__(self, m_hat: torch.Tensor, planes: int = 32, rows: int = 32):
        self.G = G = m_hat.shape[0]
        self.planes, self.rows = planes, rows
        self.m = (m_hat.to(torch.float64) / G**3).to(torch.float32).contiguous()
        self.spec = torch.empty((G, G, G // 2 + 1), device="cuda", dtype=torch.complex64)
        self.config = {"planes": planes, "rows": rows}

    def __call__(self, p_curr, p_prev, p_next):
        G, spec = self.G, self.spec
        for x0 in range(0, G, self.planes):
            sl = slice(x0, x0 + self.planes)
            spec[sl] = torch.fft.rfft2(p_curr[sl])
        for y0 in range(0, G, self.rows):
            sl = slice(y0, y0 + self.rows)
            s = torch.fft.fft(spec[:, sl], dim=0)
            s.mul_(self.m[:, sl])
            spec[:, sl] = torch.fft.ifft(s, dim=0, norm="forward")
        for x0 in range(0, G, self.planes):
            sl = slice(x0, x0 + self.planes)
            torch.sub(torch.fft.irfft2(spec[sl], s=(G, G), norm="forward"), p_prev[sl], out=p_next[sl])

    @classmethod
    def tuned(cls, m_hat, p_curr, p_prev, p_next):
        return fastest(cls.CONFIGS, lambda c: cls(m_hat, *c), lambda p: p(p_curr, p_prev, p_next), 3, 3, 6)[0]
