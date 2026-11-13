"""
2-D Circular Disc Blur Experiments (Section 5.2):
  1. Verifies minimax ripple vs. exact 2-way real separable rank N across:
     - Distinct complex Gaussians (N = 2, 4, 6, 8, 10, 12; Niemitalo presets + LP refinement),
     - Odd-rank mixed Gaussian budgets (1c + 1r at N = 3; 2c + 1r at N = 5; 3c + 1r at N = 7),
     - Repeated-rate polynomial-Gaussians (deg P >= 1, both complex and real Laguerre-Gaussians),
     and compares 2-D vs. 3-D exact separable ranks under Theorem 3.4.
  2. Demonstrates GL_N(R) conditioning on rowSpan: per-component real channels vs. nuclear-norm-optimal
     QR + symmetric eigendecomposition channels, measuring dynamic-range amplification and actual
     IEEE float16 vs. float32/float64 bokeh accuracy on an HDR specular test scene on RTX 4070 Ti Super.
  3. Benchmarks RTX 4070 Ti Super 2-D convolution throughput (direct W x W, cuFFT, and separable fp32 & fp16;
     implementations in gpu_kernels.py), checking every method against a float64 reference.

Run with --gpu-only to rerun just the GPU throughput benchmark from the stored families.
"""
import argparse
import json
import math
import os
import time
import numpy as np
import torch
import torch.nn.functional as F
from scipy.optimize import differential_evolution, linprog, minimize

import gpu_kernels as gk


# Exact equiripple complex-Gaussian presets from Olli Niemitalo's kernel-optimizer (tau = 0.2).
# Layout per component: [b, c, r0, i0] for Re[(r0 - i*i0) e^{(-b + i*c) s}] = (r0 cos(cs) + i0 sin(cs)) e^{-bs}.
NIEMITALO_PRESETS = {
    1: [(0.862325, 1.624835, 0.767583, 1.862321)],
    2: [
        (0.886528, 5.268909, 0.411259, -0.548794),
        (1.960518, 1.558213, 0.513282, 4.561110),
    ],
    3: [
        (2.176490, 5.043495, 1.621035, -2.105439),
        (1.019306, 9.027613, -0.280860, -0.162882),
        (2.815110, 1.597273, -0.366471, 10.300301),
    ],
    4: [
        (4.338459, 1.553635, -5.767909, 46.164397),
        (3.839993, 4.693183, 9.795391, -15.227561),
        (2.791880, 8.178137, -3.048324, 0.302959),
        (1.342190, 12.328289, 0.010001, 0.244650),
    ],
    5: [
        (4.892608, 1.685979, -22.356787, 85.912460),
        (4.711870, 4.998496, 35.918936, -28.875618),
        (4.052795, 8.244168, -13.212253, -1.578428),
        (2.929212, 11.900859, 0.507991, 1.816328),
        (1.512961, 16.116382, 0.138051, -0.010000),
    ],
    6: [
        (5.143778, 2.079813, -82.326596, 111.231024),
        (5.612426, 6.153387, 113.878661, 58.004879),
        (5.982921, 9.802895, 39.479083, -162.028887),
        (6.505167, 11.059237, -71.286026, 95.027069),
        (3.869579, 14.810520, 1.405746, -3.704914),
        (2.201904, 19.032909, -0.152784, -0.107988),
    ],
}


def make_disc_grid(tau: float = 0.2, dim_corner: int = 2, n_pass: int = 400, n_stop: int = 400):
    """Build passband r in [0, 1] and stopband r in [1+tau, sqrt(dim_corner)*(1+tau)] grids."""
    r_pass = np.linspace(0.0, 1.0, n_pass)
    S = 1.0 + tau
    s_stop = np.linspace(S**2, dim_corner * (S**2), n_stop)
    r_stop = np.sqrt(s_stop)
    s_all = np.concatenate([r_pass**2, s_stop])
    target = np.concatenate([np.ones_like(r_pass), np.zeros_like(r_stop)])
    return s_all, target, r_pass, r_stop


def eval_components_profile(s: np.ndarray, components):
    """
    components: list of dicts:
      {"kind": "c" | "r", "b": float, "c": float, "coeffs": [(r0, i0), (r1, i1), ...]}
      where P(s) = sum_k (r_k - i * i_k) s^k, eval = Re[P(s) e^{(-b + i c) s}].
    """
    out = np.zeros_like(s, dtype=np.float64)
    for comp in components:
        b = comp["b"]
        c = comp["c"] if comp["kind"] == "c" else 0.0
        eb = np.exp(-b * s)
        cs = np.cos(c * s)
        sn = np.sin(c * s)
        sk = np.ones_like(s)
        for rk, ik in comp["coeffs"]:
            if comp["kind"] == "c":
                out += sk * (rk * cs + ik * sn) * eb
            else:
                out += sk * rk * eb
            sk = sk * s
    return out


def multi_total_cost(d: int, components) -> int:
    """Exact d-way real separable rank from Theorem 3.4 (multiTotalCost)."""
    total = 0
    for comp in components:
        deg = len(comp["coeffs"]) - 1
        if comp["kind"] == "r":
            total += (d - 1) * deg + 1
        else:
            total += 2 * (d - 1) * deg + d
    return total


def solve_disc_minimax_lp(s_all: np.ndarray, target: np.ndarray, rate_specs):
    """
    Given rate_specs = [(kind, deg, b, c), ...], solve exact Chebyshev minimax LP:
      min t  s.t.  |B w - target| <= t.
    Returns (ripple, components).
    """
    cols = []
    for kind, deg, b, c in rate_specs:
        eb = np.exp(-b * s_all)
        cs = np.cos(c * s_all) if kind == "c" else np.ones_like(s_all)
        sn = np.sin(c * s_all) if kind == "c" else np.zeros_like(s_all)
        for k in range(deg + 1):
            sk = (s_all**k) * eb
            cols.append(sk * cs)
            if kind == "c":
                cols.append(sk * sn)
    B = np.column_stack(cols)
    n_vars = B.shape[1]
    c_obj = np.zeros(n_vars + 1)
    c_obj[-1] = 1.0
    A_ub = np.vstack([
        np.column_stack([B, -np.ones(B.shape[0])]),
        np.column_stack([-B, -np.ones(B.shape[0])]),
    ])
    b_ub = np.concatenate([target, -target])
    bounds = [(None, None)] * n_vars + [(0.0, None)]
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if not res.success:
        return 1.0, None
    w = res.x[:n_vars]
    ripple = float(res.x[-1])
    comps = []
    idx = 0
    for kind, deg, b, c in rate_specs:
        coeffs = []
        for _ in range(deg + 1):
            if kind == "c":
                coeffs.append((float(w[idx]), float(w[idx + 1])))
                idx += 2
            else:
                coeffs.append((float(w[idx]), 0.0))
                idx += 1
        comps.append({"kind": kind, "b": float(b), "c": float(c if kind == "c" else 0.0), "coeffs": coeffs})
    return ripple, comps


def optimize_disc_family(structure, tau: float = 0.2, dim_corner: int = 2, maxiter: int = 55):
    """
    structure: list of (kind, deg), e.g. [('c', 0), ('r', 0)] for (1c, 1r).
    Optimizes rate parameters via DE + Nelder-Mead with exact inner minimax LP, then evaluates on fine grid.
    """
    s_coarse, tgt_coarse, _, _ = make_disc_grid(tau=tau, dim_corner=dim_corner, n_pass=140, n_stop=140)
    s_fine, tgt_fine, _, _ = make_disc_grid(tau=tau, dim_corner=dim_corner, n_pass=1000, n_stop=1000)

    bounds = []
    for kind, deg in structure:
        bounds.append((0.3, 12.0))  # b
        if kind == "c":
            bounds.append((0.4, 22.0))  # c

    def unpack_specs(theta):
        specs = []
        p = 0
        for kind, deg in structure:
            b = theta[p]
            p += 1
            c = theta[p] if kind == "c" else 0.0
            if kind == "c":
                p += 1
            specs.append((kind, deg, b, c))
        return specs

    def obj(theta):
        specs = unpack_specs(theta)
        # Penalize colliding complex rates when multiple distinct c components are requested
        c_list = [(b, c) for kind, _, b, c in specs if kind == "c"]
        for i in range(len(c_list)):
            for j in range(i + 1, len(c_list)):
                if math.hypot(c_list[i][0] - c_list[j][0], c_list[i][1] - c_list[j][1]) < 0.25:
                    return 1.0
        rip, _ = solve_disc_minimax_lp(s_coarse, tgt_coarse, specs)
        return rip

    res = differential_evolution(obj, bounds=bounds, maxiter=maxiter, popsize=14, seed=42, polish=False)
    res2 = minimize(obj, res.x, method="Nelder-Mead", options={"maxiter": 300, "xatol": 1e-5, "fatol": 1e-7})
    best_theta = res2.x if res2.fun <= res.fun else res.x
    best_specs = unpack_specs(best_theta)
    _, comps = solve_disc_minimax_lp(s_fine, tgt_fine, best_specs)
    fine_err = float(np.max(np.abs(eval_components_profile(s_fine, comps) - tgt_fine)))
    return fine_err, comps


def per_component_channels_1d(x: np.ndarray, components, S: float = 1.2):
    """
    Construct the exact minimal-rank per-component real 1-D factors (h_n(x), v_n(y)) on grid x.
    Returns H, V of shape (N, len(x)) with K(x_i, y_j) = sum_{n=0}^{N-1} H[n, i] * V[n, j].
    """
    s = x**2
    H_list, V_list = [], []
    S2 = S**2
    for comp in components:
        b = comp["b"]
        deg = len(comp["coeffs"]) - 1
        if comp["kind"] == "r":
            eb = np.exp(-b * s)
            # P(sx + sy) = sum_{j=0}^deg sx^j * sum_{q=j}^deg C(q,j) r_q sy^{q-j}
            for j in range(deg + 1):
                hj = ((s / S2) ** j) * eb
                vj = np.zeros_like(s)
                for q in range(j, deg + 1):
                    rq = comp["coeffs"][q][0]
                    vj += math.comb(q, j) * rq * (S2**j) * (s ** (q - j)) * eb
                # Balance L2 norms of hj and vj
                nh, nv = np.linalg.norm(hj), np.linalg.norm(vj)
                if nh > 0 and nv > 0:
                    scale = math.sqrt(nv / nh)
                    hj, vj = hj * scale, vj / scale
                H_list.append(hj)
                V_list.append(vj)
        else:
            c = comp["c"]
            lam = -b + 1j * c
            elam = np.exp(lam * s)
            if deg == 0:
                a0 = comp["coeffs"][0][0] - 1j * comp["coeffs"][0][1]
                beta = np.sqrt(a0 + 0j)
                g = beta * elam
                H_list.append(np.real(g))
                V_list.append(np.real(g))
                H_list.append(np.imag(g))
                V_list.append(-np.imag(g))
            else:
                for j in range(deg + 1):
                    uj = ((s / S2) ** j) * elam
                    wj = np.zeros_like(s, dtype=np.complex128)
                    for q in range(j, deg + 1):
                        aq = comp["coeffs"][q][0] - 1j * comp["coeffs"][q][1]
                        wj += math.comb(q, j) * aq * (S2**j) * (s ** (q - j)) * elam
                    nu, nw = np.linalg.norm(uj), np.linalg.norm(wj)
                    if nu > 0 and nw > 0:
                        sc = math.sqrt(nw / nu)
                        uj, wj = uj * sc, wj / sc
                    # Re(uj * wj) = Re(uj)*Re(wj) - Im(uj)*Im(wj)
                    H_list.append(np.real(uj))
                    V_list.append(np.real(wj))
                    H_list.append(np.imag(uj))
                    V_list.append(-np.imag(wj))
    return np.array(H_list, dtype=np.float64), np.array(V_list, dtype=np.float64)


def orthogonal_rowspan_channels_1d(H_raw: np.ndarray, V_raw: np.ndarray):
    """
    Rebalance a symmetric rank-N 2-D kernel K = H_raw^T V_raw via QR + symmetric eigendecomposition
    on rowSpan(K), ordered smallest-|eigenvalue| first for low-precision accumulation.
    Achieves the nuclear-norm global minimum sum_n ||h_n||_2 ||v_n||_2 = ||K||_{S_1}.
    """
    # Stack [H_raw; V_raw]^T and orthogonalize to span row/col space cleanly, or since K is symmetric:
    # K = H_raw^T V_raw = 0.5 * (H_raw^T V_raw + V_raw^T H_raw).
    # Even simpler and exact: QR on H_raw^T (M x N) and V_raw^T, or QR on combined basis:
    Q, R_qr = np.linalg.qr(H_raw.T, mode="reduced")  # Q: (M, N), R_qr: (N, N)
    # Since colSpan(K) = rowSpan(K) has exact dimension N, V_raw @ Q spans it:
    # Check projection: K = Q @ (R_qr @ V_raw) -> since K is symmetric, K = Q @ M_sym @ Q^T
    # where M_sym = R_qr @ (V_raw @ Q)! Let's verify exactness and fall back to SVD of R_h M R_v^T if needed!
    Qv, Rv = np.linalg.qr(np.hstack([H_raw.T, V_raw.T]), mode="reduced")
    # Project K onto Qv: C_proj = (Qv^T H_raw^T) (V_raw Qv), symmetrized:
    C_sym = 0.5 * ((Qv.T @ H_raw.T) @ (V_raw @ Qv) + (Qv.T @ V_raw.T) @ (H_raw @ Qv))
    evals, evecs = np.linalg.eigh(C_sym)
    # Keep top N = H_raw.shape[0] eigenvalues by magnitude, then sort ascending by |e|!
    N = H_raw.shape[0]
    top_idx = np.argsort(np.abs(evals))[-N:]  # already sorted ascending by |e|!
    evals_n = evals[top_idx]
    evecs_n = evecs[:, top_idx]  # (dim_Q, N)
    G_orth = (Qv @ evecs_n).T  # (N, M), orthonormal rows!
    # Fix eigenvector sign gauge deterministically so DC/center lobe is positive:
    for r_idx in range(N):
        s_row = float(np.sum(G_orth[r_idx]))
        ref = s_row if abs(s_row) > 1e-8 else float(G_orth[r_idx, G_orth.shape[1] // 2])
        if ref < 0.0:
            G_orth[r_idx] = -G_orth[r_idx]
    amp = np.sqrt(np.abs(evals_n))[:, None]
    sgn = np.where(evals_n >= 0, 1.0, -1.0)[:, None]
    H_orth = amp * G_orth
    V_orth = sgn * H_orth
    return H_orth, V_orth


def linear_to_srgb(x: np.ndarray) -> np.ndarray:
    """Exact IEC 61966-2-1 linear-light [0, 1] to sRGB [0, 1] transfer function."""
    c = np.clip(x, 0.0, 1.0)
    return np.where(c <= 0.0031308, 12.92 * c, 1.055 * np.power(np.maximum(c, 1e-12), 1.0 / 2.4) - 0.055)


def unbalanced_per_component_channels_1d(x: np.ndarray, components):
    """
    Stage 1 (naive unbalanced per-component split): places polynomial/amplitude weights a_q on the
    first pass H (written into the float16 intermediate buffer) and unit-scale basis functions
    x^{2j} exp(lam x^2) on the second pass V (no sqrt(beta), S^2 rescaling, or L2 pair balancing).
    """
    s = x**2
    H_list, V_list = [], []
    for comp in components:
        b = comp["b"]
        deg = len(comp["coeffs"]) - 1
        if comp["kind"] == "r":
            eb = np.exp(-b * s)
            for j in range(deg + 1):
                uj = (s**j) * eb
                wj = np.zeros_like(s)
                for q in range(j, deg + 1):
                    rq = comp["coeffs"][q][0]
                    wj += math.comb(q, j) * rq * (s ** (q - j)) * eb
                H_list.append(wj)
                V_list.append(uj)
        else:
            c = comp["c"]
            lam = -b + 1j * c
            elam = np.exp(lam * s)
            for j in range(deg + 1):
                uj = (s**j) * elam
                wj = np.zeros_like(s, dtype=np.complex128)
                for q in range(j, deg + 1):
                    aq = comp["coeffs"][q][0] - 1j * comp["coeffs"][q][1]
                    wj += math.comb(q, j) * aq * (s ** (q - j)) * elam
                H_list.append(np.real(wj))
                V_list.append(np.real(uj))
                H_list.append(-np.imag(wj))
                V_list.append(np.imag(uj))
    return np.array(H_list, dtype=np.float64), np.array(V_list, dtype=np.float64)


def balance_channel_pairs_1d(H_in: np.ndarray, V_in: np.ndarray):
    """
    Stage 2 (pure diagonal channel-pair L2 balancing D in GL_R(R)): rescales each rank-1 channel
    (h_n, v_n) -> (c_n h_n, v_n / c_n) so ||h_n||_2 == ||v_n||_2 while keeping every rank-1 outer
    product h_n v_n^T (and hence kappa_inf and sum_n ||h_n||_2 ||v_n||_2) identically unchanged.
    """
    H_bal, V_bal = H_in.copy(), V_in.copy()
    for n in range(H_bal.shape[0]):
        nh = float(np.linalg.norm(H_bal[n]))
        nv = float(np.linalg.norm(V_bal[n]))
        if nh > 0.0 and nv > 0.0:
            scale = math.sqrt(nv / nh)
            H_bal[n] *= scale
            V_bal[n] /= scale
    return H_bal, V_bal


def make_bokeh_test_image(H_img: int = 512, W_img: int = 512, seed: int = 7, peak_hdr: float = 48.0) -> np.ndarray:
    """
    Create a realistic scene-linear HDR test image:
      - Smooth background spanning deep night shadows (0.001 linear, inside the 12.92x sRGB toe)
        up to lit midtones (0.75 linear), plus a sharp circular object edge;
      - 25 bright 3x3 HDR point glints (linear radiance in [peak_hdr/6, peak_hdr]).
    """
    rng = np.random.default_rng(seed)
    yy, xx = np.meshgrid(np.linspace(-1, 1, H_img), np.linspace(-1, 1, W_img), indexing="ij")
    img = 0.001 + 0.45 * np.power(0.5 + 0.5 * np.sin(2.5 * xx) * np.cos(2.0 * yy), 2.5)
    img += 0.30 * ((xx**2 + yy**2) < 0.20).astype(np.float64)
    for _ in range(25):
        cy = rng.integers(48, H_img - 48)
        cx = rng.integers(48, W_img - 48)
        amp = rng.uniform(peak_hdr / 6.0, peak_hdr)
        img[cy - 1 : cy + 2, cx - 1 : cx + 2] += amp
    return img


def evaluate_conditioning_ablation(families, R_px: int = 25, n_seeds: int = 20, peak_levels=(8.0, 48.0, 256.0)):
    """
    4-stage float16 sRGB bokeh conditioning ablation isolating each mechanism in `separableChannels`:
      Stage 1 (unbalanced): raw per-component channels with weights on V (no intra-term norm balance);
      Stage 2 (term_balanced): per-component channels with ||h_n||_2 == ||v_n||_2 (no GL_R rotation);
      Stage 3 (orth_desc): GL_R(R) orthogonalized rowSpan channels accumulated LARGEST-|e_n| first;
      Stage 4 (orth_asc): GL_R(R) orthogonalized rowSpan channels accumulated SMALLEST-|e_n| first.
    Evaluated across `n_seeds` random 512x512 HDR scenes (peak=48) and across `peak_levels`.
    """
    L = math.ceil(1.2 * R_px)
    x_grid = np.arange(-L, L + 1, dtype=np.float64) / R_px
    target_labels = [
        "1c (Gaussian)",
        "2c (Gaussian)",
        "1c_2 (deg 1 complex)",
        "4c (Gaussian)",
        "6c (Gaussian)",
        "1c_6 (deg 5 complex)",
    ]
    scenes_48 = [make_bokeh_test_image(512, 512, seed=s, peak_hdr=48.0) for s in range(n_seeds)]
    ablation_rows = []

    for lbl in target_labels:
        fam = next(f for f in families if f["label"] == lbl)
        comps = fam["components"]
        H_unb, V_unb = unbalanced_per_component_channels_1d(x_grid, comps)
        H_bal, V_bal = balance_channel_pairs_1d(H_unb, V_unb)
        H_asc, V_asc = orthogonal_rowspan_channels_1d(H_bal, V_bal)
        H_desc, V_desc = H_asc[::-1].copy(), V_asc[::-1].copy()

        K_ex = H_bal.T @ V_bal
        k_peak = float(np.max(np.abs(K_ex)))
        stages = [
            ("unbalanced", H_unb, V_unb),
            ("term_balanced", H_bal, V_bal),
            ("orth_desc", H_desc, V_desc),
            ("orth_asc", H_asc, V_asc),
        ]
        entry = {"label": lbl, "rank_R": fam["rank_2d"], "stages_20scenes_peak48": {}, "peak_sweep_seed7": {}}
        for st_name, Hf, Vf in stages:
            kappa_inf = float(np.sum(np.max(np.abs(Hf), axis=1) * np.max(np.abs(Vf), axis=1)) / k_peak)
            kappa_l2 = float(np.sum(np.linalg.norm(Hf, axis=1) * np.linalg.norm(Vf, axis=1)) / np.linalg.norm(K_ex, ord="nuc"))
            h_over_v = float(np.max(np.maximum(np.linalg.norm(Hf, axis=1) / np.maximum(np.linalg.norm(Vf, axis=1), 1e-30),
                                               np.linalg.norm(Vf, axis=1) / np.maximum(np.linalg.norm(Hf, axis=1), 1e-30))))
            max_srgb_list, rmse_srgb_list, max_lin_list = [], [], []
            n_overflow = 0
            for sc in scenes_48:
                rm, mx, ln = simulate_separable_blur_precision(sc, Hf, Vf, torch.float16)
                if not math.isfinite(mx):
                    n_overflow += 1
                else:
                    max_srgb_list.append(255.0 * mx)
                    rmse_srgb_list.append(255.0 * rm)
                    max_lin_list.append(255.0 * ln)
            entry["stages_20scenes_peak48"][st_name] = {
                "kappa_inf": kappa_inf,
                "nuclear_ratio": kappa_l2,
                "max_factor_imbalance": h_over_v,
                "n_overflow": n_overflow,
                "srgb_max_mean": float(np.mean(max_srgb_list)) if max_srgb_list else float("inf"),
                "srgb_max_std": float(np.std(max_srgb_list, ddof=1)) if len(max_srgb_list) > 1 else 0.0,
                "srgb_max_worst": float(np.max(max_srgb_list)) if max_srgb_list else float("inf"),
                "srgb_rmse_mean": float(np.mean(rmse_srgb_list)) if rmse_srgb_list else float("inf"),
                "srgb_rmse_std": float(np.std(rmse_srgb_list, ddof=1)) if len(rmse_srgb_list) > 1 else 0.0,
                "lin_max_mean": float(np.mean(max_lin_list)) if max_lin_list else float("inf"),
            }

        # HDR glint peak sweep at seed=7
        for pk in peak_levels:
            sc_pk = make_bokeh_test_image(512, 512, seed=7, peak_hdr=pk)
            pk_dict = {}
            for st_name, Hf, Vf in stages:
                rm, mx, ln = simulate_separable_blur_precision(sc_pk, Hf, Vf, torch.float16)
                pk_dict[st_name] = {
                    "srgb_max_255": 255.0 * mx if math.isfinite(mx) else "overflow",
                    "lin_max_255": 255.0 * ln if math.isfinite(ln) else "overflow",
                }
            entry["peak_sweep_seed7"][f"peak_{int(pk)}"] = pk_dict

        s48 = entry["stages_20scenes_peak48"]
        print(
            f"Ablation {lbl:22s} (R={fam['rank_2d']:2d}): "
            f"Unbal={s48['unbalanced']['srgb_max_mean']:7.2f}+/-{s48['unbalanced']['srgb_max_std']:4.2f} (ovf={s48['unbalanced']['n_overflow']}) | "
            f"TermBal={s48['term_balanced']['srgb_max_mean']:6.2f}+/-{s48['term_balanced']['srgb_max_std']:4.2f} | "
            f"OrthDesc={s48['orth_desc']['srgb_max_mean']:5.2f}+/-{s48['orth_desc']['srgb_max_std']:4.2f} | "
            f"OrthAsc={s48['orth_asc']['srgb_max_mean']:5.2f}+/-{s48['orth_asc']['srgb_max_std']:4.2f}"
        )
        ablation_rows.append(entry)
    return ablation_rows


def simulate_separable_blur_precision(img: np.ndarray, H_fac: np.ndarray, V_fac: np.ndarray, dtype):
    """
    Simulate 2-D separable blur in scene-linear light and measure 8-bit sRGB display error
    |sRGB(clip(acc_lp, 0, 1)) - sRGB(clip(acc_fp64, 0, 1))| (plus linear-light max error).
    """
    ksum = float(np.sum(H_fac @ np.ones(H_fac.shape[1]) * (V_fac @ np.ones(V_fac.shape[1]))))
    s_norm = 1.0 / math.sqrt(abs(ksum))
    Hn = H_fac * s_norm
    Vn = V_fac * (s_norm if ksum > 0 else -s_norm)

    device = torch.device("cuda")
    L = Hn.shape[1] // 2
    img_t = torch.tensor(img[None, None, :, :], device=device, dtype=torch.float64)

    # Exact float64 linear-light reference
    acc64 = torch.zeros_like(img_t)
    for n in range(Hn.shape[0]):
        hx = torch.tensor(Hn[n][None, None, None, :], device=device, dtype=torch.float64)
        vy = torch.tensor(Vn[n][None, None, :, None], device=device, dtype=torch.float64)
        m64 = F.conv2d(F.pad(img_t, (L, L, 0, 0), mode="replicate"), hx)
        acc64 = acc64 + F.conv2d(F.pad(m64, (0, 0, L, L), mode="replicate"), vy)

    # Target precision (e.g. torch.float16 intermediate + accumulator)
    img_lp = img_t.to(dtype)
    acc_lp = torch.zeros_like(img_lp)
    for n in range(Hn.shape[0]):
        hx = torch.tensor(Hn[n][None, None, None, :], device=device, dtype=dtype)
        vy = torch.tensor(Vn[n][None, None, :, None], device=device, dtype=dtype)
        m_lp = F.conv2d(F.pad(img_lp, (L, L, 0, 0), mode="replicate"), hx)
        acc_lp = acc_lp + F.conv2d(F.pad(m_lp, (0, 0, L, L), mode="replicate"), vy)

    a64 = acc64.cpu().numpy()[0, 0]
    alp = acc_lp.to(torch.float64).cpu().numpy()[0, 0]
    if not np.all(np.isfinite(alp)):
        return float("inf"), float("inf"), float("inf")
    srgb_diff = np.abs(linear_to_srgb(alp) - linear_to_srgb(a64))
    srgb_rmse = float(np.sqrt(np.mean(srgb_diff**2)))
    srgb_max = float(np.max(srgb_diff))
    lin_max = float(np.max(np.abs(alp - a64)))
    return srgb_rmse, srgb_max, lin_max


def optimize_discrete_disc_rank_r(R_px: int, R_rank: int, K_seed: np.ndarray, tau: float = 0.2, shell_isotropic: bool = False):
    """
    Compare sampled continuous complex-Gaussian disc kernels against three direct discrete rank-R methods
    on {-L, ..., L}^2 (L = ceil((1 + tau) * R_px)):
      1) Direct SVD (Eckart-Young l_2-optimal rank-R truncation of raised-cosine smooth disc on [1, 1+tau]);
      2) Unconstrained discrete rank-R minimax (POCS + bisection minimizing max_{r<=1 or r>=1+tau} |K - 1_{r<=1}|);
      3) Shell-isotropic discrete rank-R minimax (additionally projecting onto equal-Euclidean-radius shells).
    """
    L = math.ceil((1.0 + tau) * R_px)
    m = np.arange(-L, L + 1, dtype=np.float64)
    mx, my = np.meshgrid(m, m, indexing="ij")
    n2 = (mx**2 + my**2).astype(np.int64)
    r = np.sqrt(n2) / R_px
    mask_ps = (r <= 1.0) | (r >= 1.0 + tau)
    tgt = (r <= 1.0).astype(np.float64)

    # Raised-cosine smooth disc for direct SVD baseline
    K_rc = np.zeros_like(r)
    K_rc[r <= 1.0] = 1.0
    m_tr = (r > 1.0) & (r < 1.0 + tau)
    K_rc[m_tr] = 0.5 * (1.0 + np.cos(math.pi * (r[m_tr] - 1.0) / tau))
    U_rc, s_rc, Vt_rc = np.linalg.svd(K_rc, full_matrices=False)
    s_rc_trunc = s_rc.copy()
    s_rc_trunc[R_rank:] = 0.0
    K_svd = (U_rc * s_rc_trunc) @ Vt_rc
    K_svd = 0.5 * (K_svd + K_svd.T)
    K_svd = 0.25 * (K_svd + K_svd[::-1, :] + K_svd[:, ::-1] + K_svd[::-1, ::-1])
    U_s, s_s, Vt_s = np.linalg.svd(K_svd, full_matrices=False)
    s_s[R_rank:] = 0.0
    K_svd = (U_s * s_s) @ Vt_s

    if L + 1 <= R_rank:
        # Every even symmetric matrix on {-L..L}^2 has rank <= L + 1 <= R_rank!
        return K_svd, K_rc.copy()

    uniq_n2, inv_n2 = np.unique(n2.ravel(), return_inverse=True)
    counts_n2 = np.bincount(inv_n2)

    rip_seed = float(np.max(np.abs(K_seed[mask_ps] - tgt[mask_ps])))
    lo, hi = 0.0, rip_seed
    M_best = K_seed.copy()
    best_rip = rip_seed
    n_iters = 240 if shell_isotropic else 140
    for _ in range(14):
        mid = 0.5 * (lo + hi)
        M = M_best.copy()
        for _it in range(n_iters):
            if shell_isotropic:
                shell_avg = np.bincount(inv_n2, weights=M.ravel()) / counts_n2
                M = shell_avg[inv_n2].reshape(M.shape)
            else:
                # Preserve D_4 axis/diagonal symmetry so discrete stencil is symmetric
                M = 0.5 * (M + M.T)
                M = 0.25 * (M + M[::-1, :] + M[:, ::-1] + M[::-1, ::-1])
            M[mask_ps] = tgt[mask_ps] + np.clip(M[mask_ps] - tgt[mask_ps], -mid, mid)
            U, s, Vt = np.linalg.svd(M, full_matrices=False)
            s[R_rank:] = 0.0
            M = (U * s) @ Vt
        M = 0.5 * (M + M.T)
        M = 0.25 * (M + M[::-1, :] + M[:, ::-1] + M[::-1, ::-1])
        U, s, Vt = np.linalg.svd(M, full_matrices=False)
        s[R_rank:] = 0.0
        M_rk = (U * s) @ Vt
        ach_rip = float(np.max(np.abs(M_rk[mask_ps] - tgt[mask_ps])))
        if shell_isotropic:
            shell_avg = np.bincount(inv_n2, weights=M_rk.ravel()) / counts_n2
            M_rad = shell_avg[inv_n2].reshape(M_rk.shape)
            aniso_err = float(np.max(np.abs(M_rk - M_rad)))
            ok = (ach_rip <= mid + 2e-4) and (aniso_err <= 2e-4)
        else:
            ok = ach_rip <= mid + 1.5e-4
        if ok:
            if ach_rip <= best_rip:
                best_rip = ach_rip
                M_best = M_rk
            hi = min(hi, ach_rip)
        else:
            lo = mid
    return K_svd, M_best


def measure_kernel_anisotropy(K: np.ndarray, R_px: int, tau: float = 0.2):
    """Return (pass_stop_ripple, equal_radius_shell_spread, rim_shell_spread, dtft_anisotropy)."""
    L = K.shape[0] // 2
    m = np.arange(-L, L + 1, dtype=np.float64)
    mx, my = np.meshgrid(m, m, indexing="ij")
    n2 = (mx**2 + my**2).astype(np.int64)
    r = np.sqrt(n2) / R_px
    mask_ps = (r <= 1.0) | (r >= 1.0 + tau)
    tgt = (r <= 1.0).astype(np.float64)
    rip = float(np.max(np.abs(K[mask_ps] - tgt[mask_ps])))

    max_shell = 0.0
    max_rim = 0.0
    for val in np.unique(n2):
        rn = math.sqrt(val) / R_px
        pts = K[n2 == val]
        if len(pts) > 1 and rn <= math.sqrt(2.0) * (1.0 + tau):
            sp = float(np.max(pts) - np.min(pts))
            max_shell = max(max_shell, sp)
            if 1.0 < rn < 1.0 + tau:
                max_rim = max(max_rim, sp)

    k0 = abs(float(np.sum(K)))
    thetas = np.linspace(0.0, 0.25 * math.pi, 25)
    max_dtft = 0.0
    for kr in np.linspace(0.05, math.pi, 40):
        vals = [float(np.sum(K * np.cos(kr * math.cos(th) * mx) * np.cos(kr * math.sin(th) * my))) for th in thetas]
        max_dtft = max(max_dtft, (max(vals) - min(vals)) / max(k0, 1e-12))
    return {
        "ripple": rip,
        "shell_aniso": max_shell,
        "rim_aniso": max_rim,
        "dtft_aniso": max_dtft,
    }


def evaluate_discrete_vs_continuous(families, radii=(3, 6, 12, 25, 64), ranks=(2, 4, 8, 12)):
    """Compare sampled continuous Gaussians vs direct SVD, unconstrained discrete minimax, and shell-isotropic minimax."""
    rank_to_lbl = {2: "1c (Gaussian)", 4: "2c (Gaussian)", 8: "4c (Gaussian)", 12: "6c (Gaussian)"}
    rows = []
    saved_kernels = {}
    for R_px in radii:
        L = math.ceil(1.2 * R_px)
        x = np.arange(-L, L + 1, dtype=np.float64) / R_px
        r2 = x[:, None] ** 2 + x[None, :] ** 2
        for R_rank in ranks:
            fam = next(f for f in families if f["label"] == rank_to_lbl[R_rank])
            K_cont = eval_components_profile(r2.ravel(), fam["components"]).reshape(r2.shape)
            K_svd, K_uncon = optimize_discrete_disc_rank_r(R_px, R_rank, K_cont, tau=0.2, shell_isotropic=False)
            _, K_iso = optimize_discrete_disc_rank_r(R_px, R_rank, K_cont, tau=0.2, shell_isotropic=True)
            m_cont = measure_kernel_anisotropy(K_cont, R_px)
            m_svd = measure_kernel_anisotropy(K_svd, R_px)
            m_uncon = measure_kernel_anisotropy(K_uncon, R_px)
            m_iso = measure_kernel_anisotropy(K_iso, R_px)
            row = {
                "radius_px": R_px,
                "W_tap": 2 * L + 1,
                "even_dim": L + 1,
                "rank_R": R_rank,
                "cont": m_cont,
                "svd": m_svd,
                "disc_uncon": m_uncon,
                "disc_iso": m_iso,
            }
            rows.append(row)
            print(
                f"DiscVsCont R_px={R_px:2d} (L+1={L+1:2d}), R={R_rank:2d} | "
                f"Cont rip={m_cont['ripple']:.4f} | SVD rip={m_svd['ripple']:.4f} (aniso={m_svd['shell_aniso']:.3f}) | "
                f"Uncon rip={m_uncon['ripple']:.4f} (aniso={m_uncon['shell_aniso']:.3f}) | Iso rip={m_iso['ripple']:.4f}"
            )
            if R_rank == 4 and R_px in (6, 25):
                saved_kernels[f"Rpx{R_px}_R4"] = {
                    "cont": K_cont.tolist(),
                    "svd": K_svd.tolist(),
                    "disc_uncon": K_uncon.tolist(),
                    "disc_iso": K_iso.tolist(),
                }
    return {"summary": rows, "kernels_R4": saved_kernels}


def normalized_half_stencils(R_px: int, components):
    """
    Orthogonal rowSpan channels of a family sampled at radius R_px, scaled to unit DC gain, as half
    stencils: returns (L, Hh, Vh) with Hh, Vh of shape (N, L + 1) and K[i, j] = sum_n Hh[n, |i|] Vh[n, |j|].
    """
    L = math.ceil(1.2 * R_px)
    x = np.arange(-L, L + 1, dtype=np.float64) / R_px
    H_fac, V_fac = orthogonal_rowspan_channels_1d(*per_component_channels_1d(x, components, S=1.2))
    ksum = float(np.sum(H_fac.T @ V_fac))
    s_norm = 1.0 / math.sqrt(abs(ksum))
    H_fac, V_fac = H_fac * s_norm, V_fac * (s_norm if ksum > 0 else -s_norm)
    assert np.allclose(H_fac, H_fac[:, ::-1]) and np.allclose(V_fac, V_fac[:, ::-1])
    return L, H_fac[:, L:].copy(), V_fac[:, L:].copy()


def reference_blur64(img64: torch.Tensor, Hh: np.ndarray, Vh: np.ndarray, mode: str = "replicate") -> torch.Tensor:
    """float64 separable blur of an (H, W, C) image with `mode` ("replicate" or "constant") borders."""
    L = Hh.shape[1] - 1
    C = img64.shape[2]
    x = img64.permute(2, 0, 1)[None]
    px = F.pad(x, (L, L, 0, 0), mode=mode)
    acc = torch.zeros_like(x)
    for n in range(Hh.shape[0]):
        hx = torch.tensor(np.concatenate([Hh[n, :0:-1], Hh[n]]), device=x.device)[None, None, None, :].repeat(C, 1, 1, 1)
        vy = torch.tensor(np.concatenate([Vh[n, :0:-1], Vh[n]]), device=x.device)[None, None, :, None].repeat(C, 1, 1, 1)
        acc += F.conv2d(F.pad(F.conv2d(px, hx, groups=C), (0, 0, L, L), mode=mode), vy, groups=C)
    return acc[0].permute(1, 2, 0).contiguous()


GPU_BENCHMARK_INFO = {
    "image": "1080 x 1920 RGBA, independent uniform [0, 1) samples (torch.Generator seed 0)",
    "kernels": "sampled 2c/4c/6c complex-Gaussian disc families (ranks 4/8/12) as orthogonal rowSpan channels "
               "with unit DC gain; direct and cuFFT use the dense rank-4 kernel",
    "errors": "err_max_* and err_rms_* are absolute errors of each method's output against a float64 separable "
              "convolution with the same border rule (replicate, or zero for cufft_zero); float16 errors "
              "include rounding the input image to float16",
    "timing": "mean and standard deviation in ms over 10 CUDA-Event batches (15 calls each; direct: 2 to 5); "
              "launch parameters (config_*) are tuned by timing at start-up, and means differed by up to 6% "
              "between two complete runs, more than the within-run standard deviations",
    "direct": "Triton dense W x W convolution, several output rows per program sharing each row load",
    "cufft": "channel pairs packed as complex planes, in-place complex FFT, real even-kernel spectrum; "
             "7-smooth period chosen by timing; zero padding (period >= size + L) or replicate padding "
             "(period >= size + 2L)",
    "sep": "Triton vertical fan-out and horizontal fan-in passes with register sliding windows over "
           "L2-resident strips (float32, or float16 input, intermediates and output with float32 accumulation)",
}


def benchmark_blur2d_gpu(families, H_img: int = 1080, W_img: int = 1920, radii=(8, 16, 32, 64), ranks=(4, 8, 12)):
    """
    Benchmark 1920x1080 RGBA 2-D blur on RTX 4070 Ti Super (10 CUDA-Event batches: mean +/- std) and
    measure every method's error against a float64 reference (see GPU_BENCHMARK_INFO).
    """
    rank_to_lbl = {4: "2c (Gaussian)", 8: "4c (Gaussian)", 12: "6c (Gaussian)"}
    C = 4
    gen = torch.Generator().manual_seed(0)
    img64 = torch.rand((H_img, W_img, C), generator=gen, dtype=torch.float64).cuda()
    img32 = img64.to(torch.float32)
    out32 = torch.empty_like(img32)

    def as_pairs(t):
        return t.reshape(H_img, W_img, 2, 2).permute(2, 0, 1, 3).contiguous()

    pairs32 = as_pairs(img32)
    results = []
    for R_px in radii:
        stencils = {}
        for N_rank in ranks:
            fam = next(f for f in families if f["label"] == rank_to_lbl[N_rank])
            L, Hh, Vh = normalized_half_stencils(R_px, fam["components"])
            assert Hh.shape[0] == N_rank
            stencils[N_rank] = (Hh, Vh)
        W_tap = 2 * L + 1
        Hh0, Vh0 = stencils[ranks[0]]
        K2 = np.concatenate([Hh0[:, :0:-1], Hh0], axis=1).T @ np.concatenate([Vh0[:, :0:-1], Vh0], axis=1)
        ref0 = reference_blur64(img64, Hh0, Vh0)
        shared = {"radius_px": R_px, "L": L, "W_tap": W_tap}

        # 1. Direct dense W x W convolution in fp32 (replicate-clamped borders)
        direct = gk.DirectBlur2D.tuned(K2, img32, out32)
        out32.zero_()
        ms, std = gk.cuda_batch_stats(lambda: direct(img32, out32), warmup=3, n_batches=10, iters_per_batch=(5 if R_px <= 16 else 2))
        e_max, e_rms = gk.max_rms_error(out32, ref0)
        shared.update({"ms_direct_fp32": ms, "ms_direct_fp32_std": std, "err_max_direct_fp32": e_max,
                       "err_rms_direct_fp32": e_rms, "config_direct": direct.config})

        # 2. cuFFT with zero padding and with replicate padding (same borders as direct and separable)
        for mode, pad_mode in (("zero", "constant"), ("clamp", "replicate")):
            ref_m = ref0 if mode == "clamp" else reference_blur64(img64, Hh0, Vh0, mode=pad_mode)
            fft = gk.FFTBlur2D.tuned(K2, pairs32, mode)
            ms, std = gk.cuda_batch_stats(lambda: fft(pairs32), warmup=8, n_batches=10, iters_per_batch=15)
            e_max, e_rms = gk.max_rms_error(fft(pairs32), as_pairs(ref_m))
            shared.update({f"ms_cufft_{mode}_fp32": ms, f"ms_cufft_{mode}_fp32_std": std,
                           f"err_max_cufft_{mode}_fp32": e_max, f"err_rms_cufft_{mode}_fp32": e_rms,
                           f"config_cufft_{mode}": fft.config})
            del fft

        # 3. Separable rank-N cascades in fp32 and fp16
        for N_rank in ranks:
            Hh, Vh = stencils[N_rank]
            ref = ref0 if N_rank == ranks[0] else reference_blur64(img64, Hh, Vh)
            row = dict(shared, rank_N=N_rank)
            for dtype, key in [(torch.float32, "sep_fp32"), (torch.float16, "sep_fp16")]:
                inp_d = img64.to(dtype)
                out_d = torch.empty_like(inp_d)
                sep = gk.SeparableBlur2D.tuned(Hh, Vh, inp_d, out_d)
                out_d.zero_()
                ms, std = gk.cuda_batch_stats(lambda: sep(inp_d, out_d), warmup=8, n_batches=10, iters_per_batch=15)
                e_max, e_rms = gk.max_rms_error(out_d, ref)
                assert e_max < (1e-5 if dtype == torch.float32 else 2e-3), f"{key} error {e_max} at R_px={R_px}, N={N_rank}"
                row.update({f"ms_{key}": ms, f"ms_{key}_std": std, f"err_max_{key}": e_max, f"err_rms_{key}": e_rms,
                            f"config_{key}": sep.config})
                del sep
            assert max(row["err_max_direct_fp32"], row["err_max_cufft_zero_fp32"], row["err_max_cufft_clamp_fp32"]) < 2e-5
            print(
                f"1920x1080 RGBA R_px={R_px} (W={W_tap}), N={N_rank}: "
                f"Direct={row['ms_direct_fp32']:.2f}+/-{row['ms_direct_fp32_std']:.2f} ms (err {row['err_max_direct_fp32']:.1e}) | "
                f"cuFFT(zero/clamp)={row['ms_cufft_zero_fp32']:.3f}/{row['ms_cufft_clamp_fp32']:.3f} ms "
                f"(err {row['err_max_cufft_zero_fp32']:.1e}/{row['err_max_cufft_clamp_fp32']:.1e}) | "
                f"Sep fp32={row['ms_sep_fp32']:.3f}+/-{row['ms_sep_fp32_std']:.3f} ms (err {row['err_max_sep_fp32']:.1e}) | "
                f"Sep fp16={row['ms_sep_fp16']:.3f}+/-{row['ms_sep_fp16_std']:.3f} ms (err {row['err_max_sep_fp16']:.1e})"
            )
            results.append(row)
    return results


def benchmark_blur2d_cpu(H_img: int = 1080, W_img: int = 1920, radii=(8, 16, 32), ranks=(4, 8)):
    """Multi-core CPU reference timings (Intel Core Ultra 5 125H, float32, 5 runs: mean +/- std)."""
    from scipy.fft import next_fast_len

    C = 4
    inp_cpu = torch.randn((1, C, H_img, W_img), dtype=torch.float32)
    rows = []

    def _cpu_stats(fn, warmup: int = 1, n_runs: int = 5):
        for _ in range(warmup):
            fn()
        ts = []
        for _ in range(n_runs):
            t0 = time.perf_counter()
            fn()
            ts.append(1000.0 * (time.perf_counter() - t0))
        arr = np.array(ts, dtype=np.float64)
        return float(np.mean(arr)), float(np.std(arr, ddof=1))

    for R_px in radii:
        L = math.ceil(R_px * 1.2)
        W_tap = 2 * L + 1
        k2d = torch.randn((C, 1, W_tap, W_tap), dtype=torch.float32)
        ms_dir, std_dir = _cpu_stats(
            lambda: F.conv2d(F.pad(inp_cpu, (L, L, L, L), mode="replicate"), k2d, groups=C),
            warmup=1, n_runs=(4 if R_px <= 16 else 3),
        )
        Hr = next_fast_len(H_img + 2 * L + W_tap - 1)
        Wr = next_fast_len(W_img + 2 * L + W_tap - 1)
        kr_hat = torch.randn((1, 1, Hr, Wr // 2 + 1), dtype=torch.complex64)
        def _cpu_fft():
            pad_in = F.pad(inp_cpu, (L, L, L, L), mode="replicate")
            return torch.fft.irfft2(torch.fft.rfft2(pad_in, s=(Hr, Wr)) * kr_hat, s=(Hr, Wr))[:, :, 2 * L : 2 * L + H_img, 2 * L : 2 * L + W_img]
        ms_fft, std_fft = _cpu_stats(_cpu_fft, warmup=1, n_runs=5)

        entry = {
            "radius_px": R_px,
            "W_tap": W_tap,
            "ms_direct_fp32": ms_dir,
            "ms_direct_fp32_std": std_dir,
            "ms_rfft2_rep_fp32": ms_fft,
            "ms_rfft2_rep_fp32_std": std_fft,
            "separable": {},
        }
        for N_rank in ranks:
            h1d = [torch.randn((C, 1, 1, W_tap), dtype=torch.float32) for _ in range(N_rank)]
            v1d = [torch.randn((C, 1, W_tap, 1), dtype=torch.float32) for _ in range(N_rank)]
            def _cpu_sep():
                acc = None
                px = F.pad(inp_cpu, (L, L, 0, 0), mode="replicate")
                for n in range(N_rank):
                    m = F.conv2d(px, h1d[n], groups=C)
                    out_n = F.conv2d(F.pad(m, (0, 0, L, L), mode="replicate"), v1d[n], groups=C)
                    acc = out_n if acc is None else (acc + out_n)
                return acc
            ms_s, std_s = _cpu_stats(_cpu_sep, warmup=1, n_runs=5)
            entry["separable"][f"R_{N_rank}"] = {"ms_fp32": ms_s, "ms_fp32_std": std_s}
        print(
            f"CPU 1920x1080 RGBA R_px={R_px:2d} (W={W_tap:2d}): "
            f"Direct={ms_dir:.1f}+/-{std_dir:.1f} ms | FFT(clamp)={ms_fft:.1f}+/-{std_fft:.1f} ms | "
            f"Sep R=4={entry['separable']['R_4']['ms_fp32']:.1f} ms | Sep R=8={entry['separable']['R_8']['ms_fp32']:.1f} ms"
        )
        rows.append(entry)
    return rows


RESULTS_PATH = os.path.join(os.path.dirname(__file__), "results_blur_2d.json")
GPU_BENCH_TITLE = "\n=== RTX 4070 Ti Super 2-D Blur Throughput (10 batches: mean +/- std) ==="


def rerun_gpu_benchmark():
    """Rerun only the GPU throughput benchmark from the stored families and update the stored results."""
    with open(RESULTS_PATH, encoding="utf-8") as f:
        results = json.load(f)
    print(GPU_BENCH_TITLE)
    results["gpu_benchmark"] = benchmark_blur2d_gpu(results["families"], 1080, 1920, radii=(8, 16, 32, 64), ranks=(4, 8, 12))
    results["gpu_benchmark_info"] = GPU_BENCHMARK_INFO
    with open(RESULTS_PATH, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2)
    print(f"\nUpdated GPU benchmark in {RESULTS_PATH}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--gpu-only", action="store_true", help="rerun only the GPU throughput benchmark")
    if parser.parse_args().gpu_only:
        return rerun_gpu_benchmark()

    s2, tgt2, _, _ = make_disc_grid(tau=0.2, dim_corner=2, n_pass=1000, n_stop=1000)
    s3, tgt3, _, _ = make_disc_grid(tau=0.2, dim_corner=3, n_pass=1000, n_stop=1000)

    families = []

    # 1. Evaluate Niemitalo complex-Gaussian presets (LP/Nelder-Mead minimax-polished from article seeds)
    s_polish, tgt_polish, _, _ = make_disc_grid(tau=0.2, dim_corner=2, n_pass=300, n_stop=300)
    for c_cnt, raw_list in NIEMITALO_PRESETS.items():
        theta0 = np.array([v for (b, c, _, _) in raw_list for v in (b, c)], dtype=np.float64)

        def polish_obj(th):
            if np.any(th <= 0.05):
                return 1.0
            sp = [("c", 0, th[2 * i], th[2 * i + 1]) for i in range(c_cnt)]
            rip, _ = solve_disc_minimax_lp(s_polish, tgt_polish, sp)
            return rip

        res_p = minimize(polish_obj, theta0, method="Nelder-Mead", options={"maxiter": 350, "xatol": 1e-5, "fatol": 1e-7})
        th_best = res_p.x if res_p.fun <= polish_obj(theta0) else theta0
        sp_best = [("c", 0, th_best[2 * i], th_best[2 * i + 1]) for i in range(c_cnt)]
        _, comps = solve_disc_minimax_lp(s2, tgt2, sp_best)
        rip2 = float(np.max(np.abs(eval_components_profile(s2, comps) - tgt2)))
        rip3 = float(np.max(np.abs(eval_components_profile(s3, comps) - tgt3)))
        families.append({
            "label": f"{c_cnt}c (Gaussian)",
            "kind_group": "complex_gaussian",
            "rank_2d": multi_total_cost(2, comps),
            "rank_3d": multi_total_cost(3, comps),
            "ripple_2d": rip2,
            "ripple_3d_reuse": rip3,
            "components": comps,
        })
        print(f"Preset {c_cnt}c: 2D rank={2*c_cnt}, 3D rank={3*c_cnt}, ripple_2d={rip2:.5f} (3D corner={rip3:.5f})")

    # 2. Optimize odd-rank mixed Gaussian budgets & higher-multiplicity polynomial-Gaussians
    extra_specs = [
        ("1c+1r", "mixed_gaussian", [("c", 0), ("r", 0)]),
        ("2c+1r", "mixed_gaussian", [("c", 0), ("c", 0), ("r", 0)]),
        ("3c+1r", "mixed_gaussian", [("c", 0), ("c", 0), ("c", 0), ("r", 0)]),
        ("1c+1r_2 (deg 1 real)", "mixed_poly", [("c", 0), ("r", 1)]),
        ("1c_2 (deg 1 complex)", "complex_poly", [("c", 1)]),
        ("1c_3 (deg 2 complex)", "complex_poly", [("c", 2)]),
        ("1c_4 (deg 3 complex)", "complex_poly", [("c", 3)]),
        ("1c_6 (deg 5 complex)", "complex_poly", [("c", 5)]),
        ("1r_2 (deg 1 real)", "real_poly", [("r", 1)]),
        ("1r_3 (deg 2 real)", "real_poly", [("r", 2)]),
        ("1r_4 (deg 3 real)", "real_poly", [("r", 3)]),
        ("1r_6 (deg 5 real)", "real_poly", [("r", 5)]),
    ]
    for label, grp, struct in extra_specs:
        rip2, comps = optimize_disc_family(struct, tau=0.2, dim_corner=2)
        rip3 = float(np.max(np.abs(eval_components_profile(s3, comps) - tgt3)))
        r2 = multi_total_cost(2, comps)
        r3 = multi_total_cost(3, comps)
        families.append({
            "label": label,
            "kind_group": grp,
            "rank_2d": r2,
            "rank_3d": r3,
            "ripple_2d": rip2,
            "ripple_3d_reuse": rip3,
            "components": comps,
        })
        print(f"Opt {label:22s}: 2D rank={r2:2d}, 3D rank={r3:2d}, ripple_2d={rip2:.5f}")

    # 3. Verify numerical SVD rank == theoretical rank & test conditioning + float16 bokeh accuracy!
    R_px = 25
    L = math.ceil(R_px * 1.2)
    x_grid = np.arange(-L, L + 1, dtype=np.float64) / R_px
    bokeh_img = make_bokeh_test_image(512, 512)
    conditioning_rows = []

    print("\n=== Conditioning & float16 sRGB Bokeh Precision (R_px=25, W=61, HDR peak=48.0) ===")
    for fam in families:
        comps = fam["components"]
        H_raw, V_raw = per_component_channels_1d(x_grid, comps, S=1.2)
        H_orth, V_orth = orthogonal_rowspan_channels_1d(H_raw, V_raw)
        K_exact = H_raw.T @ V_raw
        K_orth = H_orth.T @ V_orth
        recon_err = float(np.max(np.abs(K_exact - K_orth)) / np.max(np.abs(K_exact)))

        # Numerical SVD rank check (singular values > 1e-11 * sigma_0)
        svals = np.linalg.svd(K_exact, compute_uv=False)
        num_rank = int(np.sum(svals > 1e-10 * svals[0]))
        assert num_rank == fam["rank_2d"], f"SVD rank mismatch on {fam['label']}: {num_rank} != {fam['rank_2d']}"

        # Peak channel dynamic-range amplification: (sum_n max|h_n| max|v_n|) / max|K|
        k_peak = float(np.max(np.abs(K_exact)))
        amp_raw = float(np.sum(np.max(np.abs(H_raw), axis=1) * np.max(np.abs(V_raw), axis=1)) / k_peak)
        amp_orth = float(np.sum(np.max(np.abs(H_orth), axis=1) * np.max(np.abs(V_orth), axis=1)) / k_peak)

        rmse_raw16, max_raw16, lin_raw16 = simulate_separable_blur_precision(bokeh_img, H_raw, V_raw, torch.float16)
        rmse_orth16, max_orth16, lin_orth16 = simulate_separable_blur_precision(bokeh_img, H_orth, V_orth, torch.float16)

        row = {
            "label": fam["label"],
            "kind_group": fam["kind_group"],
            "rank_2d": fam["rank_2d"],
            "ripple_2d": fam["ripple_2d"],
            "svd_rank": num_rank,
            "orth_recon_rel_err": recon_err,
            "amp_raw": amp_raw,
            "amp_orth": amp_orth,
            "fp16_rmse_raw_255": 255.0 * rmse_raw16,
            "fp16_max_raw_255": 255.0 * max_raw16,
            "fp16_rmse_orth_255": 255.0 * rmse_orth16,
            "fp16_max_orth_255": 255.0 * max_orth16,
            "fp16_lin_max_raw_255": 255.0 * lin_raw16,
            "fp16_lin_max_orth_255": 255.0 * lin_orth16,
        }
        conditioning_rows.append(row)
        print(
            f"{fam['label']:22s} (N={fam['rank_2d']:2d}, SVD={num_rank:2d}): "
            f"amp {amp_raw:9.2f} -> {amp_orth:5.2f} | "
            f"fp16 RMSE (/255): {255*rmse_raw16:9.3f} -> {255*rmse_orth16:6.3f} "
            f"(max {255*max_raw16:9.2f} -> {255*max_orth16:5.2f})"
        )

    print("\n=== 4-Stage separableChannels Conditioning Ablation (20 HDR scenes & peak sweep) ===")
    cond_ablation = evaluate_conditioning_ablation(families, R_px=25, n_seeds=20, peak_levels=(8.0, 48.0, 256.0))

    print("\n=== Direct Discrete Optimization vs Sampled Continuous Profiles ===")
    disc_vs_cont = evaluate_discrete_vs_continuous(families, radii=(3, 6, 12, 25, 64), ranks=(2, 4, 8, 12))

    print(GPU_BENCH_TITLE)
    gpu_bench = benchmark_blur2d_gpu(families, 1080, 1920, radii=(8, 16, 32, 64), ranks=(4, 8, 12))

    print("\n=== Multi-Core CPU 2-D Blur Reference Timings ===")
    cpu_bench = benchmark_blur2d_cpu(1080, 1920, radii=(8, 16, 32), ranks=(4, 8))

    # Save curves for Figure 1 as well
    r_plot = np.linspace(0.0, 1.85, 600)
    s_plot = r_plot**2
    curves = {"r": r_plot.tolist()}
    for fam in families:
        if fam["label"] in {"1c (Gaussian)", "1c+1r", "2c (Gaussian)", "1c_2 (deg 1 complex)", "4c (Gaussian)", "6c (Gaussian)", "1r_4 (deg 3 real)"}:
            curves[fam["label"]] = eval_components_profile(s_plot, fam["components"]).tolist()

    out_path = RESULTS_PATH
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "families": families,
                "conditioning": conditioning_rows,
                "conditioning_ablation": cond_ablation,
                "discrete_vs_continuous": disc_vs_cont,
                "gpu_benchmark": gpu_bench,
                "gpu_benchmark_info": GPU_BENCHMARK_INFO,
                "cpu_benchmark": cpu_bench,
                "profile_curves": curves,
            },
            f,
            indent=2,
        )
    print(f"\nSaved 2-D blur results to {out_path}")


if __name__ == "__main__":
    main()
