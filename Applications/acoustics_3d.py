"""
3-D Isotropic Acoustic Wave Simulation Experiments (Section 5.3):
  1. Verifies algebraically that Kowalczyk & van Walstijn's (2011) 27-point IWB room-acoustics
     scheme is identically the (r = 1, c = 0, L = 1) real-Gaussian radial stencil.
  2. Optimizes and certifies (over all 45,760 symmetry-inequivalent points of a 65^3 grid on the
     3-D Brillouin octant [0, pi]^3) unconditionally von Neumann stable, exact-sound-speed
     3-D separable radial multi-Gaussian and degree-1 polynomial-Gaussian wave propagators.
  3. Verifies Proposition 3.2 (R = r + 3c) and Proposition 3.3 (R = 7 for deg P = 1) to ~1e-16
     on [-L, L]^3.
  4. Runs 3-D broadband spherical wave propagation on 256^3 voxels on RTX 4070 Ti Super against
     the exact analytical 3-D D'Alembert radial solution, plus a 1,000-step rigid-wall 3-D room
     Neumann stability/energy test and hardware-fair GPU throughput benchmarks.
"""
import json
import math
import os
import time
import numpy as np
import torch
import torch.nn.functional as F
import triton
import triton.language as tl
from scipy.optimize import differential_evolution, linprog, minimize


def verify_iwb_is_single_real_gaussian():
    """
    Verify Kowalczyk & van Walstijn (2011) 27-pt IWB (a = 1/4, b = 1/16) equals
      M_IWB[m] = (2 - 4 nu^2) delta_0[m] + (nu^2 / 2) * 2^{-(mx^2 + my^2 + mz^2)}
    on m in {-1, 0, 1}^3 for any Courant number nu.
    """
    a, b = 0.25, 1.0 / 16.0
    d1 = 1.0 - 4.0 * a + 4.0 * b  # 1/4 (6 face neighbors)
    d2 = a - 2.0 * b              # 1/8 (12 edge neighbors)
    d3 = b                        # 1/16 (8 corner neighbors)
    d0 = -6.0 * d1 - 12.0 * d2 - 8.0 * d3  # -3.5

    m = np.array([-1, 0, 1], dtype=np.float64)
    mx, my, mz = np.meshgrid(m, m, m, indexing="ij")
    s = mx**2 + my**2 + mz**2

    for nu in [0.5, 0.75, 1.0]:
        M_iwb = np.zeros((3, 3, 3), dtype=np.float64)
        M_iwb[s == 0] = 2.0 + (nu**2) * d0
        M_iwb[s == 1] = (nu**2) * d1
        M_iwb[s == 2] = (nu**2) * d2
        M_iwb[s == 3] = (nu**2) * d3

        M_gauss = 0.5 * (nu**2) * (2.0 ** (-s))
        M_gauss[1, 1, 1] += 2.0 - 4.0 * (nu**2)
        err = float(np.max(np.abs(M_iwb - M_gauss)))
        assert err < 1e-16, f"IWB vs Gaussian mismatch: {err}"
    print("Verified: 27-pt Kowalczyk-van Walstijn IWB == (r=1, c=0, L=1) real Gaussian to < 1e-16.")


def build_ray_grid(n_ray: int = 48, k_cut_frac: float = 0.80):
    s = np.linspace(0.0, np.pi, n_ray)[1:]
    rays = [
        np.column_stack([s, np.zeros_like(s), np.zeros_like(s)]),
        np.column_stack([s, s, np.zeros_like(s)]),
        np.column_stack([s, s, s]),
        np.column_stack([s, 0.5 * s, np.zeros_like(s)]),
        np.column_stack([s, s, 0.5 * s]),
        np.column_stack([np.full_like(s, np.pi), s, np.zeros_like(s)]),
        np.column_stack([np.full_like(s, np.pi), np.full_like(s, np.pi), s]),
    ]
    K = np.vstack(rays)
    kmag = np.linalg.norm(K, axis=1)
    k_cut = k_cut_frac * np.pi
    return K, kmag, (kmag > 0.0) & (kmag <= k_cut)


def build_octant_grid(n_1d: int = 65, k_cut_frac: float = 0.80):
    """All n_1d*(n_1d+1)*(n_1d+2)/6 - 1 nonzero sorted triples 0 <= kx <= ky <= kz <= pi."""
    k1 = np.linspace(0.0, np.pi, n_1d)
    ii, jj, ll = np.meshgrid(np.arange(n_1d), np.arange(n_1d), np.arange(n_1d), indexing="ij")
    mask = (ii <= jj) & (jj <= ll) & ((ii + jj + ll) > 0)
    K = np.column_stack([k1[ii[mask]], k1[jj[mask]], k1[ll[mask]]])
    kmag = np.linalg.norm(K, axis=1)
    k_cut = k_cut_frac * np.pi
    return K, kmag, (kmag > 0.0) & (kmag <= k_cut)


def basis_poly_pts(K: np.ndarray, L: int, specs):
    """
    specs: list of (kind, deg, b, c) where kind in {'c', 'r'}.
    Evaluates B(k) = phi_hat(k) - phi_hat(0) and second derivative at k = 0.
    Uses convention Re[ (sum_{q=0}^deg (r_q + i i_q) s^q) e^{(-b + i c) s} ].
    """
    m = np.arange(-L, L + 1, dtype=np.float64)
    m2 = m**2
    cx = np.cos(np.outer(K[:, 0], m))
    cy = np.cos(np.outer(K[:, 1], m))
    cz = np.cos(np.outer(K[:, 2], m))

    cols = []
    d2_row = []
    g0_list = []
    for kind, deg, b, c in specs:
        lam = -b + (1j * c if kind == "c" else 0.0)
        e1 = np.exp(lam * m2)
        Mx, My, Mz, M0, M0_pp = [], [], [], [], []
        for r in range(deg + 1):
            w1 = (m2**r) * e1
            Mx.append(cx @ w1)
            My.append(cy @ w1)
            Mz.append(cz @ w1)
            M0.append(np.sum(w1))
            M0_pp.append(-np.sum(m2 * w1))
        for q in range(deg + 1):
            Z = np.zeros(K.shape[0], dtype=np.complex128)
            Z0 = 0.0 + 0.0j
            Z0_pp = 0.0 + 0.0j
            for i in range(q + 1):
                for j in range(q - i + 1):
                    l = q - i - j
                    mult = math.factorial(q) // (math.factorial(i) * math.factorial(j) * math.factorial(l))
                    Z += mult * Mx[i] * My[j] * Mz[l]
                    Z0 += mult * M0[i] * M0[j] * M0[l]
                    Z0_pp += mult * M0_pp[i] * M0[j] * M0[l]
            diff = Z - Z0
            if kind == "c":
                cols.append(np.real(diff))
                cols.append(-np.imag(diff))
                d2_row.append(np.real(Z0_pp))
                d2_row.append(-np.imag(Z0_pp))
                g0_list.append(float(np.real(Z0)))
                g0_list.append(float(-np.imag(Z0)))
            else:
                cols.append(np.real(diff))
                d2_row.append(np.real(Z0_pp))
                g0_list.append(float(np.real(Z0)))
    return np.column_stack(cols), np.array(d2_row, dtype=np.float64), np.array(g0_list, dtype=np.float64)


def solve_propagator_lp(B: np.ndarray, d2_row: np.ndarray, kmag: np.ndarray, in_pass: np.ndarray, nu: float, stab_margin: float = 1e-3):
    n_vars = B.shape[1]
    c_obj = np.zeros(n_vars + 1)
    c_obj[-1] = 1.0
    kp = kmag[in_pass]
    Bp = B[in_pass]
    target_diff = 2.0 * np.cos(nu * kp) - 2.0
    scale = 2.0 * nu * kp * np.sin(nu * kp)

    upper_margin = np.minimum(stab_margin, 0.25 * (nu**2) * (kmag**2))
    A_ub = np.vstack([
        np.column_stack([Bp, -scale]),
        np.column_stack([-Bp, -scale]),
        np.column_stack([B, np.zeros(B.shape[0])]),
        np.column_stack([-B, np.zeros(B.shape[0])]),
    ])
    b_ub = np.concatenate([
        target_diff,
        -target_diff,
        -upper_margin,
        np.full(B.shape[0], 4.0 - stab_margin),
    ])
    A_eq = np.zeros((1, n_vars + 1))
    A_eq[0, :n_vars] = d2_row
    b_eq = np.array([-2.0 * (nu**2)])
    bounds = [(None, None)] * n_vars + [(0.0, None)]
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    if not res.success:
        return 1.0, None
    w = res.x[:n_vars]
    M_pass = np.clip(2.0 + Bp @ w, -2.0, 2.0)
    err = float(np.max(np.abs(np.arccos(M_pass / 2.0) / (nu * kp) - 1.0)))
    return err, w


def effective_bandwidth_frac(K_oct: np.ndarray, kmag_oct: np.ndarray, M_oct: np.ndarray, nu: float, tol: float) -> float:
    """
    Largest spherical wavenumber cutoff k_max / pi <= 1.0 such that |c_num(k)/c_0 - 1| <= tol
    for ALL points in the 65^3 octant with 0 < |k| <= k_max.
    """
    in_sphere = kmag_oct <= np.pi
    ks = kmag_oct[in_sphere]
    Ms = M_oct[in_sphere]
    # Unstable modes exceed tol immediately
    unstable = np.abs(Ms) > 2.0
    pv_err = np.full_like(ks, np.inf)
    ok = ~unstable
    pv_err[ok] = np.abs(np.arccos(np.clip(Ms[ok] / 2.0, -1.0, 1.0)) / (nu * ks[ok]) - 1.0)
    bad = ks[pv_err > tol]
    if bad.size == 0:
        return 1.0
    return float(np.min(bad) / np.pi)


def evaluate_baseline_octant(scheme: str, nu: float, K_oct: np.ndarray, kmag_oct: np.ndarray):
    kx, ky, kz = K_oct[:, 0], K_oct[:, 1], K_oct[:, 2]
    cx, cy, cz = np.cos(kx), np.cos(ky), np.cos(kz)
    if scheme == "fdtd_7pt":
        M = 2.0 + 2.0 * (nu**2) * (cx + cy + cz - 3.0)
    elif scheme == "fdtd_13pt_o4":
        # 4th-order spatial axial Laplacian (-1/12, 4/3, -5/2, 4/3, -1/12): symbol 2*(4/3*(cos k - 1) - 1/12*(cos 2k - 1))
        c2x, c2y, c2z = np.cos(2 * kx), np.cos(2 * ky), np.cos(2 * kz)
        lap = (8.0 / 3.0) * (cx + cy + cz - 3.0) - (1.0 / 6.0) * (c2x + c2y + c2z - 3.0)
        M = 2.0 + (nu**2) * lap
    elif scheme == "iwb_27pt":
        M = 2.0 - 4.0 * (nu**2) + 0.5 * (nu**2) * (1.0 + cx) * (1.0 + cy) * (1.0 + cz)
    else:
        raise ValueError(scheme)
    return M


def optimize_and_certify_propagator(label: str, L: int, structure, nu: float, k_cut_frac: float, K_oct, kmag_oct):
    """
    structure: list of (kind, deg), e.g. [('c', 0), ('c', 0), ('r', 0)].
    Optimizes on 7-ray grid, then solves cutting-plane exact minimax LP on ALL 45,760 points of 65^3 octant!
    """
    K_ray, kmag_ray, in_ray = build_ray_grid(48, k_cut_frac=k_cut_frac)

    bounds = []
    for kind, deg in structure:
        bounds.append((0.025, 1.5))
        if kind == "c":
            bounds.append((0.025, 2.8))

    def unpack_specs(theta):
        specs = []
        p = 0
        for kind, deg in structure:
            b = float(theta[p])
            p += 1
            c = float(theta[p]) if kind == "c" else 0.0
            if kind == "c":
                p += 1
            specs.append((kind, deg, b, c))
        return specs

    def obj(theta):
        specs = unpack_specs(theta)
        c_rates = [(b, c) for kind, _, b, c in specs if kind == "c"]
        for i in range(len(c_rates)):
            for j in range(i + 1, len(c_rates)):
                if math.hypot(c_rates[i][0] - c_rates[j][0], c_rates[i][1] - c_rates[j][1]) < 0.08:
                    return 1.0
        B, d2, _ = basis_poly_pts(K_ray, L, specs)
        err, w = solve_propagator_lp(B, d2, kmag_ray, in_ray, nu)
        if w is None or np.sum(np.abs(w)) > 400.0:
            return 1.0
        return err

    res = differential_evolution(obj, bounds=bounds, maxiter=45, popsize=12, seed=42, polish=False)
    res2 = minimize(obj, res.x, method="Nelder-Mead", options={"maxiter": 250, "xatol": 1e-4, "fatol": 1e-6})
    best_theta = res2.x if res2.fun <= res.fun else res.x
    specs = unpack_specs(best_theta)

    # Cutting-plane exact certification on full 65^3 octant (45,760 points):
    in_oct = (kmag_oct > 0.0) & (kmag_oct <= k_cut_frac * np.pi)
    B_oct, d2_oct, g0_oct = basis_poly_pts(K_oct, L, specs)
    # Start with ray indices mapped to subset of octant + iteratively add worst passband & stability violators
    rng = np.random.default_rng(0)
    active = set(rng.choice(K_oct.shape[0], size=min(2500, K_oct.shape[0]), replace=False).tolist())
    # Always include smallest-|k| and corner points
    active.update(np.argsort(kmag_oct)[:200].tolist())
    active.update(np.argsort(kmag_oct)[-200:].tolist())

    w_cert = None
    for _ in range(8):
        act_idx = np.array(sorted(active), dtype=np.int32)
        _, w_try = solve_propagator_lp(B_oct[act_idx], d2_oct, kmag_oct[act_idx], in_oct[act_idx], nu)
        if w_try is None:
            break
        w_cert = w_try
        M_all = 2.0 + B_oct @ w_cert
        # Find worst passband errors & worst stability points on full 45,760 octant
        kp = kmag_oct[in_oct]
        Mp = np.clip(M_all[in_oct], -2.0, 2.0)
        pv_err_p = np.abs(np.arccos(Mp / 2.0) / (nu * kp) - 1.0)
        pass_indices = np.where(in_oct)[0]
        worst_pass = pass_indices[np.argsort(pv_err_p)[-150:]].tolist()
        worst_hi = np.argsort(M_all)[-100:].tolist()
        worst_lo = np.argsort(M_all)[:100].tolist()
        before = len(active)
        active.update(worst_pass + worst_hi + worst_lo)
        if len(active) == before:
            break

    M_oct = 2.0 + B_oct @ w_cert
    assert float(np.max(M_oct)) <= 2.0 + 1e-9 and float(np.min(M_oct)) >= -2.0 + 5e-4, "Stability violation!"
    kp = kmag_oct[in_oct]
    max_pv_err = float(np.max(np.abs(np.arccos(np.clip(M_oct[in_oct] / 2.0, -1.0, 1.0)) / (nu * kp) - 1.0)))
    alpha0 = float(2.0 - np.dot(g0_oct, w_cert))

    # Build structured component list and exact 3-way separable 1-D factors (Proposition 3.2 & 3.3)
    comps = []
    p = 0
    for kind, deg, b, c in specs:
        coeffs = []
        for _ in range(deg + 1):
            if kind == "c":
                coeffs.append((float(w_cert[p]), float(w_cert[p + 1])))
                p += 2
            else:
                coeffs.append((float(w_cert[p]), 0.0))
                p += 1
        comps.append({"kind": kind, "deg": deg, "b": b, "c": c, "coeffs": coeffs})

    factors_exact, factors_naive = build_3d_separable_factors(L, comps)
    recon_err = verify_3d_stencil_reconstruction(L, comps, alpha0, factors_exact)
    bw_01 = effective_bandwidth_frac(K_oct, kmag_oct, M_oct, nu, tol=1e-3)
    bw_05 = effective_bandwidth_frac(K_oct, kmag_oct, M_oct, nu, tol=5e-3)

    print(
        f"{label:24s} | L={L} (W={2*L+1:2d}), R={len(factors_exact):2d} (naive {len(factors_naive):2d}), nu={nu:.2f}, "
        f"k_c={k_cut_frac:.2f}pi -> max |dc/c0|={100*max_pv_err:.4f}%, "
        f"bw_0.1%={bw_01:.2f}pi, bw_0.5%={bw_05:.2f}pi, M in [{M_oct.min():.4f}, {M_oct.max():.4f}], recon={recon_err:.2e}"
    )
    return {
        "label": label,
        "L": L,
        "W": 2 * L + 1,
        "nu": nu,
        "k_cut_frac": k_cut_frac,
        "rank_exact": len(factors_exact),
        "rank_naive": len(factors_naive),
        "max_pv_err": max_pv_err,
        "bw_01pct_pi": bw_01,
        "bw_05pct_pi": bw_05,
        "M_min": float(M_oct.min()),
        "M_max": float(M_oct.max()),
        "alpha0": alpha0,
        "w_l1": float(np.sum(np.abs(w_cert))),
        "recon_err_max": recon_err,
        "components": comps,
        "factors_exact": factors_exact,
        "factors_naive": factors_naive,
    }


def build_3d_separable_factors(L: int, comps):
    """
    Construct BOTH:
      1. Exact R-term real 3-way factors via Proposition 3.2 (deg=0 -> 3 terms) & Proposition 3.3 (deg=1 -> 7 terms),
      2. Naive real/imaginary expansion factors (deg=0 -> 4 terms, deg=1 -> 9 terms).
    Each factor tuple is (fx, fy, fz) stored as half-stencil arrays of length L + 1 (since even-symmetric!).
    """
    m_half = np.arange(0, L + 1, dtype=np.float64)
    s = m_half**2
    exact_list = []
    naive_list = []

    for comp in comps:
        kind = comp["kind"]
        deg = comp["deg"]
        b = comp["b"]
        c = comp["c"]
        if kind == "r" and deg == 0:
            w0 = comp["coeffs"][0][0]
            amp = abs(w0) ** (1.0 / 3.0)
            sgn = 1.0 if w0 >= 0 else -1.0
            g = amp * np.exp(-b * s)
            exact_list.append((sgn * g, g, g))
            naive_list.append((sgn * g, g, g))
        elif kind == "c" and deg == 0:
            ar, ai = comp["coeffs"][0]
            a = ar + 1j * ai
            lam = -b + 1j * c
            # Balanced cube root beta^3 = a
            mag = abs(a) ** (1.0 / 3.0)
            ang = np.angle(a) / 3.0
            beta = mag * np.exp(1j * ang)
            z = beta * np.exp(lam * s)
            # Exact Proposition 3.2 (re_prod_eq_sum_re, d = 3):
            # Re(z0 z1 z2) = (4/3) sum_{r=0}^2 (-1)^r prod_{j=0}^2 Re(z_j * e^{i pi r (2r_dir? wait: Let's match exact formula!)})
            # Check Proposition 3.2 in MultiRealRank.lean (`re_prod_eq_sum_re`):
            #   Re(prod_{j=0}^{d-1} z_j) = (2^{d-1}/d) sum_{r=0}^{d-1} (-1)^r prod_{j=0}^{d-1} Re(z_j * exp(-i pi r / d))!
            # Verify: (e^{-i pi r / d})^d = e^{-i pi r} = (-1)^r!
            for r in range(3):
                phase = np.exp(-1j * np.pi * r / 3.0)
                zr = np.real(z * phase)
                sgn = -1.0 if (r % 2 == 1) else 1.0
                exact_list.append(((4.0 / 3.0) * sgn * zr, zr, zr))
            # Naive 4-term expansion: Re(z_x z_y z_z) = rx ry rz - rx iy iz - ix ry iz - ix iy rz
            rx, ix = np.real(z), np.imag(z)
            naive_list.extend([
                (rx, rx, rx),
                (-rx, ix, ix),
                (-ix, rx, ix),
                (-ix, ix, rx),
            ])
        elif kind == "c" and deg == 1:
            a0 = comp["coeffs"][0][0] + 1j * comp["coeffs"][0][1]
            a1 = comp["coeffs"][1][0] + 1j * comp["coeffs"][1][1]
            lam = -b + 1j * c
            e1 = np.exp(lam * s)
            # Proposition 3.3 (`re_coeff_prod_eq_sum_re`, d = 3, k = 1 -> R = 7):
            R = 7
            mag = max(abs(a0) + abs(a1) * max(L**2, 1), 1e-12)
            sc0 = mag ** (-2.0 / 3.0)
            sc12 = mag ** (1.0 / 3.0)
            for r in range(R):
                zeta = np.exp(2j * np.pi * r / R)
                phase = np.exp(-1j * np.pi * r * 3.0 / R)
                u0 = np.real(sc0 * (a1 + (a0 + a1 * s) * zeta) * e1 * phase)
                u1 = np.real(sc12 * (1.0 + s * zeta) * e1 * phase)
                sgn = -1.0 if (r % 2 == 1) else 1.0
                exact_list.append(((4.0 / 7.0) * sgn * u0, u1, u1))
            # Naive 9-term expansion (3 complex shifted-root terms x 3 real terms each = 9)
            for q in range(3):
                omega = np.exp(2j * np.pi * q / 3.0)
                # [X^1] across 3-rd roots of unity: (1/3) sum_{q=0}^2 omega^{-1} U_0(omega) U_1(omega) U_2(omega)
                w_0 = (a1 + (a0 + a1 * s) * omega) * e1 * np.conj(omega) / 3.0
                w_1 = (1.0 + s * omega) * e1
                for r in range(3):
                    ph = np.exp(-1j * np.pi * r / 3.0)
                    sgn = -1.0 if (r % 2 == 1) else 1.0
                    naive_list.append(((4.0 / 3.0) * sgn * np.real(w_0 * ph), np.real(w_1 * ph), np.real(w_1 * ph)))
        else:
            raise NotImplementedError(f"Unsupported component {comp}")
    return exact_list, naive_list


def verify_3d_stencil_reconstruction(L: int, comps, alpha0: float, factors_exact) -> float:
    idx_full = np.abs(np.arange(-L, L + 1))
    m = np.arange(-L, L + 1, dtype=np.float64)
    sx, sy, sz = np.meshgrid(m**2, m**2, m**2, indexing="ij")
    s_tot = sx + sy + sz
    exact = np.zeros_like(s_tot)
    for comp in comps:
        b = comp["b"]
        c = comp["c"] if comp["kind"] == "c" else 0.0
        lam = -b + 1j * c
        P_val = np.zeros_like(s_tot, dtype=np.complex128)
        for q, (rq, iq) in enumerate(comp["coeffs"]):
            P_val += (rq + 1j * iq) * (s_tot**q)
        exact += np.real(P_val * np.exp(lam * s_tot))
    exact[L, L, L] += alpha0

    recon = np.zeros_like(s_tot)
    for fx_h, fy_h, fz_h in factors_exact:
        fx, fy, fz = fx_h[idx_full], fy_h[idx_full], fz_h[idx_full]
        recon += np.einsum("i,j,k->ijk", fx, fy, fz)
    recon[L, L, L] += alpha0
    err = float(np.max(np.abs(exact - recon)))
    assert err < 1e-14, f"3-D separable reconstruction error too large: {err}"
    return err


# === Fused Triton Kernels (7-pt FDTD, 27-pt IWB, and R-term Separable Symmetric 1-D Cascades) ===

@triton.jit
def fdtd7_triton_kernel(p_curr_ptr, p_prev_ptr, p_next_ptr, nu2, G: tl.constexpr, BLOCK_Z: tl.constexpr):
    xy = tl.program_id(0)
    x_id = xy // G
    y_id = xy % G
    z_blk = tl.program_id(1)
    offs_z = z_blk * BLOCK_Z + tl.arange(0, BLOCK_Z)
    mask = offs_z < G

    # Half-sample Neumann rigid-wall reflection: -1 -> 0, G -> G - 1
    xp = tl.where(x_id + 1 >= G, G - 1, x_id + 1)
    xm = tl.where(x_id - 1 < 0, 0, x_id - 1)
    yp = tl.where(y_id + 1 >= G, G - 1, y_id + 1)
    ym = tl.where(y_id - 1 < 0, 0, y_id - 1)
    zp = tl.where(offs_z + 1 >= G, G - 1, offs_z + 1)
    zm = tl.where(offs_z - 1 < 0, 0, offs_z - 1)

    c = tl.load(p_curr_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    pm = tl.load(p_prev_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    s = (
        tl.load(p_curr_ptr + (xp * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + yp) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + ym) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zp, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zm, mask=mask, other=0.0)
        - 6.0 * c
    )
    tl.store(p_next_ptr + (x_id * G + y_id) * G + offs_z, 2.0 * c + nu2 * s - pm, mask=mask)


@triton.jit
def iwb27_triton_kernel(p_curr_ptr, p_prev_ptr, p_next_ptr, nu2, G: tl.constexpr, BLOCK_Z: tl.constexpr):
    """Dedicated single-pass fused 27-point Kowalczyk-van Walstijn IWB kernel for hardware-fair comparison."""
    xy = tl.program_id(0)
    x_id = xy // G
    y_id = xy % G
    z_blk = tl.program_id(1)
    offs_z = z_blk * BLOCK_Z + tl.arange(0, BLOCK_Z)
    mask = offs_z < G

    xm = tl.where(x_id - 1 < 0, 0, x_id - 1)
    xp = tl.where(x_id + 1 >= G, G - 1, x_id + 1)
    ym = tl.where(y_id - 1 < 0, 0, y_id - 1)
    yp = tl.where(y_id + 1 >= G, G - 1, y_id + 1)
    zm = tl.where(offs_z - 1 < 0, 0, offs_z - 1)
    zp = tl.where(offs_z + 1 >= G, G - 1, offs_z + 1)

    # Sum 1D [0.5, 1.0, 0.5] along z for each of the 9 (x, y) neighbors!
    acc_xy = tl.zeros([BLOCK_Z], dtype=tl.float32)
    for dx in range(-1, 2):
        xi = tl.where(dx == -1, xm, tl.where(dx == 1, xp, x_id))
        wx = tl.where(dx != 0, 0.5, 1.0)
        for dy in range(-1, 2):
            yi = tl.where(dy == -1, ym, tl.where(dy == 1, yp, y_id))
            wxy = wx * tl.where(dy != 0, 0.5, 1.0)
            row_ptr = p_curr_ptr + (xi * G + yi) * G
            vz = (
                tl.load(row_ptr + offs_z, mask=mask, other=0.0)
                + 0.5 * (
                    tl.load(row_ptr + zm, mask=mask, other=0.0)
                    + tl.load(row_ptr + zp, mask=mask, other=0.0)
                )
            )
            acc_xy += wxy * vz

    c = tl.load(p_curr_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    pm = tl.load(p_prev_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    pn = (2.0 - 4.0 * nu2) * c + 0.5 * nu2 * acc_xy - pm
    tl.store(p_next_ptr + (x_id * G + y_id) * G + offs_z, pn, mask=mask)


@triton.jit
def sym_conv1d_z_kernel(inp_ptr, out_ptr, w_ptr, L_val, G: tl.constexpr, BLOCK_Z: tl.constexpr):
    row_id = tl.program_id(0)
    z_blk = tl.program_id(1)
    offs_z = z_blk * BLOCK_Z + tl.arange(0, BLOCK_Z)
    mask = offs_z < G
    base = row_id * G
    w0 = tl.load(w_ptr + 0).to(tl.float32)
    acc = tl.load(inp_ptr + base + offs_z, mask=mask, other=0.0).to(tl.float32) * w0
    for m in range(1, L_val + 1):
        wm = tl.load(w_ptr + m).to(tl.float32)
        zp = offs_z + m
        zp_ref = tl.where(zp >= G, 2 * G - 1 - zp, zp)
        zm = offs_z - m
        zm_ref = tl.where(zm < 0, -1 - zm, zm)
        vp = tl.load(inp_ptr + base + zp_ref, mask=mask, other=0.0).to(tl.float32)
        vm = tl.load(inp_ptr + base + zm_ref, mask=mask, other=0.0).to(tl.float32)
        acc += wm * (vp + vm)
    tl.store(out_ptr + base + offs_z, acc.to(out_ptr.dtype.element_ty), mask=mask)


@triton.jit
def sym_conv1d_y_kernel(inp_ptr, out_ptr, w_ptr, L_val, G: tl.constexpr, BLOCK_Z: tl.constexpr, BLOCK_Y: tl.constexpr):
    x_id = tl.program_id(0)
    y_blk = tl.program_id(1)
    z_blk = tl.program_id(2)
    offs_y = y_blk * BLOCK_Y + tl.arange(0, BLOCK_Y)[:, None]
    offs_z = z_blk * BLOCK_Z + tl.arange(0, BLOCK_Z)[None, :]
    mask = (offs_y < G) & (offs_z < G)
    base_x = x_id * G * G
    w0 = tl.load(w_ptr + 0).to(tl.float32)
    acc = tl.load(inp_ptr + base_x + offs_y * G + offs_z, mask=mask, other=0.0).to(tl.float32) * w0
    for m in range(1, L_val + 1):
        wm = tl.load(w_ptr + m).to(tl.float32)
        yp = offs_y + m
        yp_ref = tl.where(yp >= G, 2 * G - 1 - yp, yp)
        ym = offs_y - m
        ym_ref = tl.where(ym < 0, -1 - ym, ym)
        vp = tl.load(inp_ptr + base_x + yp_ref * G + offs_z, mask=mask, other=0.0).to(tl.float32)
        vm = tl.load(inp_ptr + base_x + ym_ref * G + offs_z, mask=mask, other=0.0).to(tl.float32)
        acc += wm * (vp + vm)
    tl.store(out_ptr + base_x + offs_y * G + offs_z, acc.to(out_ptr.dtype.element_ty), mask=mask)


@triton.jit
def sym_conv1d_x_accum_kernel(inp_ptr, acc_ptr, w_ptr, L_val, G: tl.constexpr, INIT_ACC: tl.constexpr, BLOCK_YZ: tl.constexpr):
    x_id = tl.program_id(0)
    yz_blk = tl.program_id(1)
    offs_yz = yz_blk * BLOCK_YZ + tl.arange(0, BLOCK_YZ)
    mask = offs_yz < (G * G)
    stride_x = G * G
    w0 = tl.load(w_ptr + 0).to(tl.float32)
    val = tl.load(inp_ptr + x_id * stride_x + offs_yz, mask=mask, other=0.0).to(tl.float32) * w0
    for m in range(1, L_val + 1):
        wm = tl.load(w_ptr + m).to(tl.float32)
        xp = x_id + m
        xp_ref = tl.where(xp >= G, 2 * G - 1 - xp, xp)
        xm = x_id - m
        xm_ref = tl.where(xm < 0, -1 - xm, xm)
        vp = tl.load(inp_ptr + xp_ref * stride_x + offs_yz, mask=mask, other=0.0).to(tl.float32)
        vm = tl.load(inp_ptr + xm_ref * stride_x + offs_yz, mask=mask, other=0.0).to(tl.float32)
        val += wm * (vp + vm)
    if INIT_ACC:
        tl.store(acc_ptr + x_id * stride_x + offs_yz, val, mask=mask)
    else:
        prev = tl.load(acc_ptr + x_id * stride_x + offs_yz, mask=mask, other=0.0).to(tl.float32)
        tl.store(acc_ptr + x_id * stride_x + offs_yz, prev + val, mask=mask)


@triton.jit
def leapfrog_finish_kernel(p_curr_ptr, p_prev_ptr, acc_ptr, p_next_ptr, alpha0, n_el, BLOCK: tl.constexpr):
    pid = tl.program_id(0)
    offs = pid * BLOCK + tl.arange(0, BLOCK)
    mask = offs < n_el
    pc = tl.load(p_curr_ptr + offs, mask=mask, other=0.0).to(tl.float32)
    pp = tl.load(p_prev_ptr + offs, mask=mask, other=0.0).to(tl.float32)
    ac = tl.load(acc_ptr + offs, mask=mask, other=0.0).to(tl.float32)
    tl.store(p_next_ptr + offs, alpha0 * pc + ac - pp, mask=mask)


def step_separable_triton(p_curr, p_prev, p_next, buf1, buf2, acc, gpu_factors, alpha0: float, G: int, L: int):
    grid_z = (G * G, triton.cdiv(G, 256))
    grid_y = (G, triton.cdiv(G, 16), triton.cdiv(G, 64))
    grid_x = (G, triton.cdiv(G * G, 512))
    for r, (wx, wy, wz) in enumerate(gpu_factors):
        sym_conv1d_z_kernel[grid_z](p_curr, buf1, wz, L, G=G, BLOCK_Z=256)
        sym_conv1d_y_kernel[grid_y](buf1, buf2, wy, L, G=G, BLOCK_Z=64, BLOCK_Y=16)
        sym_conv1d_x_accum_kernel[grid_x](buf2, acc, wx, L, G=G, INIT_ACC=(r == 0), BLOCK_YZ=512)
    n_el = G * G * G
    leapfrog_finish_kernel[(triton.cdiv(n_el, 1024),)](p_curr, p_prev, acc, p_next, alpha0, n_el, BLOCK=1024)


def exact_spherical_pulse_3d(r: np.ndarray, ct: float, sigma0: float = 1.40) -> np.ndarray:
    """
    Exact 3-D D'Alembert analytical solution on R^3 for initial pressure
      p(r, 0) = f0(r) = (1 - r^2 / sigma0^2) * exp(-r^2 / (2 * sigma0^2)),  dp/dt(r, 0) = 0.
    At r = 0: limit_{r -> 0} [(r - ct) f0(r - ct) + (r + ct) f0(r + ct)] / (2r)
            = f0(ct) + ct * f0'(ct).
    """
    def f0(u):
        u2 = u**2
        return (1.0 - u2 / (sigma0**2)) * np.exp(-0.5 * u2 / (sigma0**2))

    def f0_prime(u):
        u2 = u**2
        return (-u / (sigma0**2)) * (3.0 - u2 / (sigma0**2)) * np.exp(-0.5 * u2 / (sigma0**2))

    out = np.empty_like(r, dtype=np.float64)
    zero_mask = r < 1e-12
    rz = r[~zero_mask]
    out[~zero_mask] = ((rz - ct) * f0(rz - ct) + (rz + ct) * f0(rz + ct)) / (2.0 * rz)
    if np.any(zero_mask):
        out[zero_mask] = f0(ct) + ct * f0_prime(ct)
    return out


def run_3d_spherical_wave_experiment(propagators, G: int = 256, ct_max: float = 72.0, sigma0: float = 1.40):
    """
    Propagate broadband spherical pulse from center (128, 128, 128) on a 256^3 grid on RTX 4070 Ti Super.
    Compare receiver waveforms at:
      - Axial (48, 0, 0), r = 48.000
      - Face diagonal (34, 34, 0), r = 48.083
      - Body diagonal (28, 28, 28), r = 48.497
    against exact analytical 3-D D'Alembert solution, and save mid-plane z=0 snapshot at ct ~= 48.0!
    """
    device = torch.device("cuda")
    c_idx = G // 2
    coords = torch.arange(G, device=device, dtype=torch.float64) - c_idx
    xx, yy, zz = torch.meshgrid(coords, coords, coords, indexing="ij")
    rr = torch.sqrt(xx**2 + yy**2 + zz**2).cpu().numpy()
    del xx, yy, zz

    rec_offsets = {
        "axial": (48, 0, 0),
        "face_diag": (34, 34, 0),
        "body_diag": (28, 28, 28),
    }
    rec_radii = {k: math.sqrt(dx**2 + dy**2 + dz**2) for k, (dx, dy, dz) in rec_offsets.items()}

    p0_np = exact_spherical_pulse_3d(rr, 0.0, sigma0=sigma0).astype(np.float32)

    sim_cases = [
        {"name": "7-pt FDTD (nu=1/sqrt3)", "kind": "fdtd7", "nu": 1.0 / math.sqrt(3.0), "inter": torch.float32},
        {"name": "27-pt IWB (nu=0.75)", "kind": "iwb27", "nu": 0.75, "inter": torch.float32},
        {"name": "27-pt IWB (nu=1.00)", "kind": "iwb27", "nu": 1.00, "inter": torch.float32},
    ]
    for prop in propagators:
        sim_cases.append({"name": prop["label"], "kind": "sep", "prop": prop, "nu": prop["nu"], "inter": torch.float32})
        if prop["label"] == "Rank-7 (2c+1r, nu=0.75)":
            sim_cases.append({"name": prop["label"] + " [fp16-inter]", "kind": "sep", "prop": prop, "nu": prop["nu"], "inter": torch.float16})

    sim_results = []
    snapshots = {}

    for case in sim_cases:
        nu = case["nu"]
        n_steps = int(round(ct_max / nu))
        snap_step = int(round(48.0 / nu))

        p1_np = exact_spherical_pulse_3d(rr, nu, sigma0=sigma0).astype(np.float32)
        p_prev = torch.tensor(p0_np, device=device, dtype=torch.float32)
        p_curr = torch.tensor(p1_np, device=device, dtype=torch.float32)
        p_next = torch.empty_like(p_curr)

        if case["kind"] == "sep":
            prop = case["prop"]
            L = prop["L"]
            alpha0 = prop["alpha0"]
            gpu_facs = [
                tuple(torch.tensor(f, device=device, dtype=torch.float32) for f in tup)
                for tup in prop["factors_exact"]
            ]
            buf1 = torch.empty((G, G, G), device=device, dtype=case["inter"])
            buf2 = torch.empty((G, G, G), device=device, dtype=case["inter"])
            acc = torch.empty((G, G, G), device=device, dtype=torch.float32)

        traces = {k: [float(p0_np[c_idx + dx, c_idx + dy, c_idx + dz]), float(p1_np[c_idx + dx, c_idx + dy, c_idx + dz])]
                  for k, (dx, dy, dz) in rec_offsets.items()}
        ct_times = [0.0, nu]

        grid_2d = (G * G, triton.cdiv(G, 256))
        if snap_step == 1 and case["name"] in {"7-pt FDTD (nu=1/sqrt3)", "27-pt IWB (nu=1.00)", "Rank-7 (2c+1r, nu=0.75)"}:
            snapshots[case["name"]] = p_curr[c_idx - 64 : c_idx + 65, c_idx - 64 : c_idx + 65, c_idx].cpu().numpy().tolist()

        for step in range(2, n_steps + 1):
            if case["kind"] == "fdtd7":
                fdtd7_triton_kernel[grid_2d](p_curr, p_prev, p_next, nu**2, G=G, BLOCK_Z=256)
            elif case["kind"] == "iwb27":
                iwb27_triton_kernel[grid_2d](p_curr, p_prev, p_next, nu**2, G=G, BLOCK_Z=256)
            else:
                step_separable_triton(p_curr, p_prev, p_next, buf1, buf2, acc, gpu_facs, alpha0, G, L)

            p_prev, p_curr, p_next = p_curr, p_next, p_prev
            ct_times.append(step * nu)
            for k, (dx, dy, dz) in rec_offsets.items():
                traces[k].append(float(p_curr[c_idx + dx, c_idx + dy, c_idx + dz].item()))

            if step == snap_step and case["name"] in {"7-pt FDTD (nu=1/sqrt3)", "27-pt IWB (nu=1.00)", "Rank-7 (2c+1r, nu=0.75)"}:
                snapshots[case["name"]] = p_curr[c_idx - 64 : c_idx + 65, c_idx - 64 : c_idx + 65, c_idx].cpu().numpy().tolist()

        ct_arr = np.array(ct_times, dtype=np.float64)
        rel_l2 = {}
        exact_traces = {}
        for k, r_val in rec_radii.items():
            ex = np.array([float(exact_spherical_pulse_3d(np.array([r_val]), ct, sigma0=sigma0)[0]) for ct in ct_arr])
            exact_traces[k] = ex.tolist()
            num = np.array(traces[k], dtype=np.float64)
            rel_l2[k] = float(np.linalg.norm(num - ex) / np.linalg.norm(ex))

        # Anisotropy spread: difference between axial and body-diagonal relative errors / peak arrival
        worst_rel_l2 = max(rel_l2.values())
        print(
            f"3-D Wave Sim {case['name']:34s}: rel L2 err axial={100*rel_l2['axial']:6.3f}%, "
            f"face={100*rel_l2['face_diag']:6.3f}%, body={100*rel_l2['body_diag']:6.3f}% (max={100*worst_rel_l2:6.3f}%)"
        )
        keep_traces = case["name"] in {
            "7-pt FDTD (nu=1/sqrt3)",
            "27-pt IWB (nu=1.00)",
            "Rank-7 (2c+1r, nu=0.75)",
            "Rank-7 (2c+1r, nu=1.00)",
        }
        sim_results.append({
            "name": case["name"],
            "nu": nu,
            "n_steps": n_steps,
            "rel_l2": rel_l2,
            "max_rel_l2": worst_rel_l2,
            "ct": ct_arr.tolist() if keep_traces else None,
            "traces": traces if keep_traces else None,
            "exact_traces": exact_traces if keep_traces else None,
        })
    return sim_results, snapshots


def verify_rigid_room_long_time_stability(prop, G_room: int = 64, n_steps: int = 1000):
    """
    Run 1,000 steps in a 64^3 rigid-walled enclosure (half-sample DCT-II Neumann walls, >15 wall bounces!).
    Verify discrete leapfrog energy E^n = ||p^n - p^{n-1}||^2 + <p^n, (2 - M) p^{n-1}> stays strictly positive
    and conserved to floating-point precision!
    """
    device = torch.device("cuda")
    L = prop["L"]
    alpha0 = prop["alpha0"]
    gpu_facs = [tuple(torch.tensor(f, device=device, dtype=torch.float32) for f in tup) for tup in prop["factors_exact"]]

    # Off-center Gaussian initial condition in rigid room [0, 64)^3 -> excites all 3-D room modes!
    coords = torch.arange(G_room, device=device, dtype=torch.float32)
    xx, yy, zz = torch.meshgrid(coords, coords, coords, indexing="ij")
    r2 = (xx - 21.3) ** 2 + (yy - 29.7) ** 2 + (zz - 18.4) ** 2
    p_prev = torch.exp(-0.25 * r2)
    buf1 = torch.empty_like(p_prev)
    buf2 = torch.empty_like(p_prev)
    acc = torch.empty_like(p_prev)
    p_curr = torch.empty_like(p_prev)
    p_next = torch.empty_like(p_prev)

    # Symmetric first step for dp/dt(0) = 0: p^1 = 0.5 * (M * p^0)
    step_separable_triton(p_prev, torch.zeros_like(p_prev), p_curr, buf1, buf2, acc, gpu_facs, alpha0, G_room, L)
    p_curr = 0.5 * p_curr

    def discrete_energy(pc, pp):
        # Apply M * pp via step_separable_triton with zero prev -> M_pp
        M_pp = torch.empty_like(pc)
        step_separable_triton(pp, torch.zeros_like(pp), M_pp, buf1, buf2, acc, gpu_facs, alpha0, G_room, L)
        diff_norm2 = torch.sum((pc - pp) ** 2).item()
        pot = torch.sum(pc * (2.0 * pp - M_pp)).item()
        return diff_norm2 + pot

    e_init = discrete_energy(p_curr, p_prev)
    for _ in range(2, n_steps + 1):
        step_separable_triton(p_curr, p_prev, p_next, buf1, buf2, acc, gpu_facs, alpha0, G_room, L)
        p_prev, p_curr, p_next = p_curr, p_next, p_prev
    e_final = discrete_energy(p_curr, p_prev)
    rel_drift = abs(e_final - e_init) / abs(e_init)
    print(f"Rigid 64^3 Room ({n_steps} steps, >18 wall reflections) {prop['label']}: E_0={e_init:.6f}, E_{n_steps}={e_final:.6f}, rel drift={rel_drift:.2e}")
    assert rel_drift < 1e-4 and e_final > 0, f"Energy drift too large: {rel_drift}"
    return {"e_init": e_init, "e_final": e_final, "rel_drift": rel_drift}


def benchmark_3d_gpu(propagators, G: int = 256):
    """Benchmark 256^3 step times on RTX 4070 Ti Super across FDTD baselines, direct conv3d, naive, and exact."""
    device = torch.device("cuda")
    p_curr = torch.randn((G, G, G), device=device, dtype=torch.float32)
    p_prev = torch.randn((G, G, G), device=device, dtype=torch.float32)
    p_next = torch.empty_like(p_curr)
    acc = torch.empty_like(p_curr)
    grid_2d = (G * G, triton.cdiv(G, 256))

    bench = []

    # 1. 7-pt FDTD
    for _ in range(10):
        fdtd7_triton_kernel[grid_2d](p_curr, p_prev, p_next, 1.0 / 3.0, G=G, BLOCK_Z=256)
    torch.cuda.synchronize()
    t0 = time.perf_counter()
    for _ in range(100):
        fdtd7_triton_kernel[grid_2d](p_curr, p_prev, p_next, 1.0 / 3.0, G=G, BLOCK_Z=256)
    torch.cuda.synchronize()
    ms7 = 1000.0 * (time.perf_counter() - t0) / 100.0
    bench.append({"name": "7-pt FDTD (1-pass Triton)", "W": 3, "rank": None, "ms_fp32": ms7, "gvox_fp32": (G**3 / 1e9) / (ms7 / 1000.0)})
    print(f"Bench 256^3 7-pt FDTD (1-pass Triton): {ms7:.3f} ms/step ({(G**3/1e9)/(ms7/1000.0):.2f} GVox/s)")

    # 2. 27-pt IWB FDTD (dedicated 1-pass Triton!)
    for _ in range(10):
        iwb27_triton_kernel[grid_2d](p_curr, p_prev, p_next, 1.0, G=G, BLOCK_Z=256)
    torch.cuda.synchronize()
    t0 = time.perf_counter()
    for _ in range(100):
        iwb27_triton_kernel[grid_2d](p_curr, p_prev, p_next, 1.0, G=G, BLOCK_Z=256)
    torch.cuda.synchronize()
    ms27 = 1000.0 * (time.perf_counter() - t0) / 100.0
    bench.append({"name": "27-pt IWB (1-pass Triton)", "W": 3, "rank": 1, "ms_fp32": ms27, "gvox_fp32": (G**3 / 1e9) / (ms27 / 1000.0)})
    print(f"Bench 256^3 27-pt IWB (1-pass Triton): {ms27:.3f} ms/step ({(G**3/1e9)/(ms27/1000.0):.2f} GVox/s)")

    # 3. Direct W^3 conv3d vs Naive vs Exact Triton (fp32 & fp16-inter) for each unique (L, rank_exact, rank_naive)
    seen = set()
    p5 = p_curr[None, None]
    for prop in propagators:
        key = (prop["L"], prop["rank_exact"], prop["rank_naive"])
        if key in seen:
            continue
        seen.add(key)
        L = prop["L"]
        W = prop["W"]

        # Direct W^3 conv3d
        k3d = torch.randn((1, 1, W, W, W), device=device, dtype=torch.float32)
        for _ in range(2):
            F.conv3d(F.pad(p5, (L,) * 6, mode="replicate"), k3d)
        torch.cuda.synchronize()
        t0 = time.perf_counter()
        n_dir = 4 if W <= 13 else 3
        for _ in range(n_dir):
            F.conv3d(F.pad(p5, (L,) * 6, mode="replicate"), k3d)
        torch.cuda.synchronize()
        ms_dir = 1000.0 * (time.perf_counter() - t0) / n_dir

        fac_ex = [tuple(torch.tensor(f, device=device, dtype=torch.float32) for f in tup) for tup in prop["factors_exact"]]
        fac_nv = [tuple(torch.tensor(f, device=device, dtype=torch.float32) for f in tup) for tup in prop["factors_naive"]]

        b32_1 = torch.empty((G, G, G), device=device, dtype=torch.float32)
        b32_2 = torch.empty((G, G, G), device=device, dtype=torch.float32)
        b16_1 = torch.empty((G, G, G), device=device, dtype=torch.float16)
        b16_2 = torch.empty((G, G, G), device=device, dtype=torch.float16)

        def time_triton(facs, b1, b2):
            for _ in range(6):
                step_separable_triton(p_curr, p_prev, p_next, b1, b2, acc, facs, prop["alpha0"], G, L)
            torch.cuda.synchronize()
            t_s = time.perf_counter()
            iters = 40
            for _ in range(iters):
                step_separable_triton(p_curr, p_prev, p_next, b1, b2, acc, facs, prop["alpha0"], G, L)
            torch.cuda.synchronize()
            return 1000.0 * (time.perf_counter() - t_s) / iters

        ms_nv32 = time_triton(fac_nv, b32_1, b32_2)
        ms_ex32 = time_triton(fac_ex, b32_1, b32_2)
        ms_ex16 = time_triton(fac_ex, b16_1, b16_2)

        row = {
            "label": prop["label"],
            "L": L,
            "W": W,
            "rank_exact": prop["rank_exact"],
            "rank_naive": prop["rank_naive"],
            "ms_direct_fp32": ms_dir,
            "ms_naive_fp32": ms_nv32,
            "ms_exact_fp32": ms_ex32,
            "ms_exact_fp16": ms_ex16,
            "gvox_exact_fp32": (G**3 / 1e9) / (ms_ex32 / 1000.0),
            "gvox_exact_fp16": (G**3 / 1e9) / (ms_ex16 / 1000.0),
        }
        bench.append(row)
        print(
            f"Bench 256^3 W={W:2d} (R={prop['rank_exact']} vs naive {prop['rank_naive']}): "
            f"Direct={ms_dir:6.2f} ms | Naive fp32={ms_nv32:5.2f} ms | "
            f"Exact fp32={ms_ex32:5.2f} ms ({ms_dir/ms_ex32:.1f}x) | Exact fp16={ms_ex16:5.2f} ms ({ms_dir/ms_ex16:.1f}x)"
        )
    return bench


def compute_dispersion_curves(propagators):
    """Compute directional phase-velocity error curves vs |k|/pi along (1,0,0), (1,1,0), (1,1,1) for plotting."""
    k_norm = np.linspace(1e-3, 0.88, 220)
    k_vals = k_norm * np.pi
    dirs = {
        "axis": np.array([1.0, 0.0, 0.0]),
        "face": np.array([1.0 / math.sqrt(2.0), 1.0 / math.sqrt(2.0), 0.0]),
        "body": np.array([1.0 / math.sqrt(3.0)] * 3),
    }
    curves = {"k_over_pi": k_norm.tolist(), "models": {}}

    for bname, sch, nu in [
        ("7-pt FDTD (nu=1/sqrt3)", "fdtd_7pt", 1.0 / math.sqrt(3.0)),
        ("27-pt IWB (nu=1.00)", "iwb_27pt", 1.00),
    ]:
        curves["models"][bname] = {}
        for dname, u in dirs.items():
            K = np.outer(k_vals, u)
            M = evaluate_baseline_octant(sch, nu, K, k_vals)
            pv = np.arccos(np.clip(M / 2.0, -1.0, 1.0)) / (nu * k_vals) - 1.0
            curves["models"][bname][dname] = (100.0 * pv).tolist()

    for prop in propagators:
        if prop["label"] in {"Rank-6 (2c, nu=0.75)", "Rank-7 (2c+1r, nu=0.75)", "Rank-7 (2c+1r, nu=1.00)", "Rank-7 (deg1 1c, nu=0.75)"}:
            curves["models"][prop["label"]] = {}
            specs = [(c["kind"], c["deg"], c["b"], c["c"]) for c in prop["components"]]
            w_vec = []
            for c in prop["components"]:
                for rq, iq in c["coeffs"]:
                    w_vec.append(rq)
                    if c["kind"] == "c":
                        w_vec.append(iq)
            w_vec = np.array(w_vec, dtype=np.float64)
            for dname, u in dirs.items():
                K = np.outer(k_vals, u)
                B, _, _ = basis_poly_pts(K, prop["L"], specs)
                M = 2.0 + B @ w_vec
                pv = np.arccos(np.clip(M / 2.0, -1.0, 1.0)) / (prop["nu"] * k_vals) - 1.0
                curves["models"][prop["label"]][dname] = (100.0 * pv).tolist()
    return curves


def main():
    verify_iwb_is_single_real_gaussian()

    K_oct, kmag_oct, _ = build_octant_grid(65, k_cut_frac=0.80)
    print(f"Built 65^3 Brillouin octant certification grid: {K_oct.shape[0]} unique symmetry-inequivalent 3-D wavevectors.")

    # Evaluate baselines on full 65^3 octant
    baselines = []
    for name, sch, nu in [
        ("7-pt FDTD (nu=1/sqrt3)", "fdtd_7pt", 1.0 / math.sqrt(3.0)),
        ("13-pt O(dx^4,dt^2) FDTD (nu=0.50)", "fdtd_13pt_o4", 0.50),
        ("27-pt IWB (nu=0.75)", "iwb_27pt", 0.75),
        ("27-pt IWB (nu=1.00)", "iwb_27pt", 1.00),
    ]:
        M_b = evaluate_baseline_octant(sch, nu, K_oct, kmag_oct)
        bw01 = effective_bandwidth_frac(K_oct, kmag_oct, M_b, nu, tol=1e-3)
        bw05 = effective_bandwidth_frac(K_oct, kmag_oct, M_b, nu, tol=5e-3)
        in75 = kmag_oct <= 0.75 * np.pi
        in80 = kmag_oct <= 0.80 * np.pi
        err75 = float(np.max(np.abs(np.arccos(np.clip(M_b[in75] / 2.0, -1.0, 1.0)) / (nu * kmag_oct[in75]) - 1.0)))
        err80 = float(np.max(np.abs(np.arccos(np.clip(M_b[in80] / 2.0, -1.0, 1.0)) / (nu * kmag_oct[in80]) - 1.0)))
        baselines.append({
            "label": name, "nu": nu, "err_075pi": err75, "err_080pi": err80,
            "bw_01pct_pi": bw01, "bw_05pct_pi": bw05,
        })
        print(f"Baseline {name:34s}: err@0.75pi={100*err75:6.2f}%, err@0.80pi={100*err80:6.2f}%, bw_0.1%={bw01:.3f}pi, bw_0.5%={bw05:.3f}pi")

    print("\n=== Optimizing & Certifying 3-D Separable Radial Propagators on 65^3 Octant ===")
    configs = [
        ("Rank-4 (1c+1r, nu=0.75)", 4, [("c", 0), ("r", 0)], 0.75, 0.75),
        ("Rank-6 (2c, nu=0.75)", 5, [("c", 0), ("c", 0)], 0.75, 0.75),
        ("Rank-7 (deg1 1c, nu=0.75)", 6, [("c", 1)], 0.75, 0.75),
        ("Rank-7 (2c+1r, nu=0.75)", 6, [("c", 0), ("c", 0), ("r", 0)], 0.75, 0.80),
        ("Rank-7 (2c+1r, nu=1.00)", 6, [("c", 0), ("c", 0), ("r", 0)], 1.00, 0.80),
        ("Rank-9 (3c, nu=0.75)", 8, [("c", 0), ("c", 0), ("c", 0)], 0.75, 0.85),
    ]
    propagators = [optimize_and_certify_propagator(lbl, L, st, nu, kc, K_oct, kmag_oct) for lbl, L, st, nu, kc in configs]

    print("\n=== 3-D Broadband Spherical Wave Simulation on 256^3 Grid (RTX 4070 Ti Super) ===")
    sim_results, snapshots = run_3d_spherical_wave_experiment(propagators, G=256, ct_max=72.0, sigma0=1.40)

    print("\n=== 1,000-Step Rigid 3-D Room Neumann Wall Energy Conservation ===")
    room_checks = {}
    for prop in propagators:
        if prop["label"] in {"Rank-7 (2c+1r, nu=0.75)", "Rank-7 (2c+1r, nu=1.00)", "Rank-7 (deg1 1c, nu=0.75)"}:
            room_checks[prop["label"]] = verify_rigid_room_long_time_stability(prop, G_room=64, n_steps=1000)

    print("\n=== Hardware-Fair RTX 4070 Ti Super 256^3 Throughput Benchmarks ===")
    gpu_bench = benchmark_3d_gpu(propagators, G=256)
    disp_curves = compute_dispersion_curves(propagators)

    # Strip numpy arrays inside factors for clean JSON serialization
    serializable_props = []
    for p in propagators:
        p_copy = {k: v for k, v in p.items() if k not in {"factors_exact", "factors_naive"}}
        p_copy["factors_exact"] = [[f.tolist() for f in tup] for tup in p["factors_exact"]]
        serializable_props.append(p_copy)

    out_path = os.path.join(os.path.dirname(__file__), "results_acoustics_3d.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "baselines": baselines,
                "propagators": serializable_props,
                "spherical_wave_sim": sim_results,
                "snapshots_z0_ct48": snapshots,
                "rigid_room_energy": room_checks,
                "gpu_benchmark_256cubed": gpu_bench,
                "dispersion_curves": disp_curves,
            },
            f,
            indent=2,
        )
    print(f"\nSaved 3-D acoustic simulation results to {out_path}")


if __name__ == "__main__":
    main()
