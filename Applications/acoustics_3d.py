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
     Neumann stability/energy test and hardware-fair GPU throughput benchmarks (separable, direct
     and k-space steps from gpu_kernels.py, each checked against a float64 step).

Run with --gpu-only to rerun just the GPU parts (wave simulation, room test and throughput benchmarks)
from the stored propagators.
"""
import argparse
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

import gpu_kernels as gk


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


def build_octant_unit_dirs(n_bary: int = 16) -> np.ndarray:
    """153 unit vectors covering the symmetry-reduced octant 0 <= ux <= uy <= uz, ||u||_2 = 1."""
    pts = []
    for i in range(n_bary + 1):
        for j in range(i, n_bary + 1):
            for l in range(j, n_bary + 1):
                if i + j + l == 0:
                    continue
                v = np.array([i, j, l], dtype=np.float64)
                pts.append(v / np.linalg.norm(v))
    arr = np.unique(np.round(np.array(pts), 12), axis=0)
    return arr / np.linalg.norm(arr, axis=1, keepdims=True)


def build_ray_grid(n_ray: int = 48, k_cut_frac: float = 0.80):
    s = np.unique(np.concatenate([
        np.linspace(0.0, np.pi, n_ray)[1:],
        np.linspace(0.02 * np.pi, k_cut_frac * np.pi, 32),
        np.array([k_cut_frac * np.pi]),
    ]))
    u_coarse = build_octant_unit_dirs(4)  # ~19 octant directions including (1,0,0), (1,1,0), (1,1,1), (1,1.5,1)
    rays = []
    for u in u_coarse:
        r_max_box = np.pi / np.max(u)
        rs = s[s <= r_max_box + 1e-12]
        rays.append(np.outer(rs, u))
    rays.extend([
        np.column_stack([np.full_like(s, np.pi), s, np.zeros_like(s)]),
        np.column_stack([np.full_like(s, np.pi), np.full_like(s, np.pi), s]),
    ])
    K = np.vstack(rays)
    kmag = np.linalg.norm(K, axis=1)
    k_cut = k_cut_frac * np.pi
    return K, kmag, (kmag > 0.0) & (kmag <= k_cut + 1e-12)


def build_octant_grid(n_1d: int = 65, k_cut_frac: float = 0.80):
    """
    Combined Brillouin-octant verification set:
      - All n_1d*(n_1d+1)*(n_1d+2)/6 - 1 nonzero sorted Cartesian triples in [0, pi]^3, PLUS
      - Dense spherical-octant shells (250 radii in (0, pi] including exact 0.75pi, 0.80pi, 0.85pi
        across 153 octant unit directions).
    """
    k1 = np.linspace(0.0, np.pi, n_1d)
    ii, jj, ll = np.meshgrid(np.arange(n_1d), np.arange(n_1d), np.arange(n_1d), indexing="ij")
    mask = (ii <= jj) & (jj <= ll) & ((ii + jj + ll) > 0)
    K_cart = np.column_stack([k1[ii[mask]], k1[jj[mask]], k1[ll[mask]]])

    u_dirs = build_octant_unit_dirs(16)
    radii = np.unique(np.concatenate([
        np.linspace(0.004 * np.pi, np.pi, 250),
        np.array([0.75 * np.pi, 0.80 * np.pi, 0.85 * np.pi]),
    ]))
    K_sph = np.einsum("r,du->rdu", radii, u_dirs).reshape(-1, 3)
    K_sph = K_sph[np.max(K_sph, axis=1) <= np.pi + 1e-12]

    K = np.vstack([K_cart, K_sph])
    kmag = np.linalg.norm(K, axis=1)
    k_cut = k_cut_frac * np.pi
    return K, kmag, (kmag > 0.0) & (kmag <= k_cut + 1e-12)


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


def effective_bandwidth_frac_fn(eval_M_fn, nu: float, tol: float, u_dirs: np.ndarray) -> float:
    """
    Conservative spherical wavenumber cutoff k_max / pi <= 1.0 such that |c_num(k)/c_0 - 1| <= tol
    across all 153 octant directions, refined by 24-step bisection between the last passing shell
    and the first failing shell.
    """
    radii = np.linspace(0.002 * np.pi, np.pi, 500)
    K_all = np.einsum("r,du->rdu", radii, u_dirs).reshape(-1, 3)
    M_all = eval_M_fn(K_all).reshape(len(radii), len(u_dirs))
    unstable = np.abs(M_all) > 2.0
    pv_err = np.full_like(M_all, np.inf)
    ok = ~unstable
    r_bcast = np.broadcast_to(radii[:, None], M_all.shape)
    pv_err[ok] = np.abs(np.arccos(np.clip(M_all[ok] / 2.0, -1.0, 1.0)) / (nu * r_bcast[ok]) - 1.0)
    shell_worst = np.max(pv_err, axis=1)
    bad_idx = np.where(shell_worst > tol)[0]
    if bad_idx.size == 0:
        return 1.0
    first_bad = int(bad_idx[0])
    if first_bad == 0:
        return 0.0
    r_lo = float(radii[first_bad - 1])
    r_hi = float(radii[first_bad])
    for _ in range(24):
        r_mid = 0.5 * (r_lo + r_hi)
        M_mid = eval_M_fn(r_mid * u_dirs)
        if np.any(np.abs(M_mid) > 2.0):
            r_hi = r_mid
        else:
            err_mid = float(np.max(np.abs(np.arccos(np.clip(M_mid / 2.0, -1.0, 1.0)) / (nu * r_mid) - 1.0)))
            if err_mid <= tol:
                r_lo = r_mid
            else:
                r_hi = r_mid
    return r_lo / np.pi


def continuous_refine_max_pv_err(eval_M_fn, K_pass: np.ndarray, pv_err_grid: np.ndarray, nu: float, k_cut: float) -> float:
    """Multi-start continuous Nelder-Mead refinement from top 20 passband grid peaks on 0 < ||k||_2 <= k_cut."""
    best = float(np.max(pv_err_grid))
    top_idx = np.argsort(pv_err_grid)[-20:]

    def neg_err_sph(sph):
        r, th, ph = sph
        if r <= 1e-5 or r > k_cut or th < 0.0 or th > 0.5 * np.pi or ph < 0.0 or ph > 0.5 * np.pi:
            return 1.0
        kv = np.array([[r * math.sin(th) * math.cos(ph), r * math.sin(th) * math.sin(ph), r * math.cos(th)]])
        mv = float(eval_M_fn(kv)[0])
        if abs(mv) > 2.0:
            return -10.0
        return -abs(math.acos(max(-1.0, min(1.0, mv / 2.0))) / (nu * r) - 1.0)

    for idx in top_idx:
        kx, ky, kz = K_pass[idx]
        r0 = math.sqrt(kx * kx + ky * ky + kz * kz)
        th0 = math.acos(max(-1.0, min(1.0, kz / r0)))
        ph0 = math.atan2(ky, max(kx, 1e-15))
        res = minimize(neg_err_sph, np.array([min(r0, k_cut - 1e-7), th0, ph0]),
                       method="Nelder-Mead", options={"maxiter": 180, "xatol": 1e-6, "fatol": 1e-9})
        if -res.fun > best and -res.fun < 5.0:
            best = float(-res.fun)
    return best


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
    elif scheme == "fdtd_25pt_o4":
        # Exact O(dx^4, dt^4) fourth-order compact explicit 25-point scheme (Tuomela / Hamilton & Bilbao 2016):
        # Matches 2 cos(nu ||k||_2) through O(k^4) in all 3-D directions; CFL limit nu_max = 1 / sqrt(3).
        c2x, c2y, c2z = np.cos(2 * kx), np.cos(2 * ky), np.cos(2 * kz)
        c1 = (8.0 / 3.0) * (nu**2) - 2.0 * (nu**4)
        c2 = ((nu**4) - (nu**2)) / 6.0
        c11 = (2.0 / 3.0) * (nu**4)
        M = 2.0 + c1 * (cx + cy + cz - 3.0) + c2 * (c2x + c2y + c2z - 3.0) + c11 * (cx * cy + cy * cz + cz * cx - 3.0)
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
    in_oct = (kmag_oct > 0.0) & (kmag_oct <= k_cut_frac * np.pi + 1e-12)
    B_oct, d2_oct, g0_oct = basis_poly_pts(K_oct, L, specs)
    rng = np.random.default_rng(0)
    active = set(rng.choice(K_oct.shape[0], size=min(3000, K_oct.shape[0]), replace=False).tolist())
    active.update(np.argsort(kmag_oct)[:250].tolist())
    active.update(np.argsort(kmag_oct)[-250:].tolist())
    bdry_idx = np.where(np.abs(kmag_oct - k_cut_frac * np.pi) < 1e-9)[0].tolist()
    active.update(bdry_idx)

    w_cert = None
    for _ in range(25):
        act_idx = np.array(sorted(active), dtype=np.int32)
        lp_err, w_try = solve_propagator_lp(B_oct[act_idx], d2_oct, kmag_oct[act_idx], in_oct[act_idx], nu)
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
    grid_pv_err = np.abs(np.arccos(np.clip(M_oct[in_oct] / 2.0, -1.0, 1.0)) / (nu * kp) - 1.0)
    eval_M_prop = lambda K_q: 2.0 + basis_poly_pts(K_q, L, specs)[0] @ w_cert
    max_pv_err = continuous_refine_max_pv_err(eval_M_prop, K_oct[in_oct], grid_pv_err, nu, k_cut_frac * np.pi)
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
    u_dirs = build_octant_unit_dirs(16)
    bw_01 = effective_bandwidth_frac_fn(eval_M_prop, nu, tol=1e-3, u_dirs=u_dirs)
    bw_05 = effective_bandwidth_frac_fn(eval_M_prop, nu, tol=5e-3, u_dirs=u_dirs)

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


# === Fused single-pass Triton kernels for the compact FDTD baselines (7-pt, 13-pt, 27-pt IWB, 25-pt) ===

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
def fdtd13_o4_triton_kernel(p_curr_ptr, p_prev_ptr, p_next_ptr, nu2, G: tl.constexpr, BLOCK_Z: tl.constexpr):
    """Fused single-pass 13-point O(dx^4, dt^2) axial FDTD kernel with half-sample Neumann reflection."""
    xy = tl.program_id(0)
    x_id = xy // G
    y_id = xy % G
    z_blk = tl.program_id(1)
    offs_z = z_blk * BLOCK_Z + tl.arange(0, BLOCK_Z)
    mask = offs_z < G

    xm1 = tl.where(x_id - 1 < 0, -1 - (x_id - 1), x_id - 1)
    xp1 = tl.where(x_id + 1 >= G, 2 * G - 1 - (x_id + 1), x_id + 1)
    xm2 = tl.where(x_id - 2 < 0, -1 - (x_id - 2), x_id - 2)
    xp2 = tl.where(x_id + 2 >= G, 2 * G - 1 - (x_id + 2), x_id + 2)

    ym1 = tl.where(y_id - 1 < 0, -1 - (y_id - 1), y_id - 1)
    yp1 = tl.where(y_id + 1 >= G, 2 * G - 1 - (y_id + 1), y_id + 1)
    ym2 = tl.where(y_id - 2 < 0, -1 - (y_id - 2), y_id - 2)
    yp2 = tl.where(y_id + 2 >= G, 2 * G - 1 - (y_id + 2), y_id + 2)

    zm1 = tl.where(offs_z - 1 < 0, -1 - (offs_z - 1), offs_z - 1)
    zp1 = tl.where(offs_z + 1 >= G, 2 * G - 1 - (offs_z + 1), offs_z + 1)
    zm2 = tl.where(offs_z - 2 < 0, -1 - (offs_z - 2), offs_z - 2)
    zp2 = tl.where(offs_z + 2 >= G, 2 * G - 1 - (offs_z + 2), offs_z + 2)

    c = tl.load(p_curr_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    pm = tl.load(p_prev_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    s1 = (
        tl.load(p_curr_ptr + (xp1 * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm1 * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + yp1) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + ym1) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zp1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zm1, mask=mask, other=0.0)
    )
    s2 = (
        tl.load(p_curr_ptr + (xp2 * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm2 * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + yp2) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + ym2) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zp2, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zm2, mask=mask, other=0.0)
    )
    lap = (4.0 / 3.0) * s1 - (1.0 / 12.0) * s2 - 7.5 * c
    tl.store(p_next_ptr + (x_id * G + y_id) * G + offs_z, 2.0 * c + nu2 * lap - pm, mask=mask)


@triton.jit
def fdtd25_o4_triton_kernel(p_curr_ptr, p_prev_ptr, p_next_ptr, w0, w_face, w_ax2, w_edge, G: tl.constexpr, BLOCK_Z: tl.constexpr):
    """Fused single-pass 25-point O(dx^4, dt^4) compact explicit FDTD kernel (Hamilton & Bilbao 2016)."""
    xy = tl.program_id(0)
    x_id = xy // G
    y_id = xy % G
    z_blk = tl.program_id(1)
    offs_z = z_blk * BLOCK_Z + tl.arange(0, BLOCK_Z)
    mask = offs_z < G

    xm1 = tl.where(x_id - 1 < 0, -1 - (x_id - 1), x_id - 1)
    xp1 = tl.where(x_id + 1 >= G, 2 * G - 1 - (x_id + 1), x_id + 1)
    xm2 = tl.where(x_id - 2 < 0, -1 - (x_id - 2), x_id - 2)
    xp2 = tl.where(x_id + 2 >= G, 2 * G - 1 - (x_id + 2), x_id + 2)

    ym1 = tl.where(y_id - 1 < 0, -1 - (y_id - 1), y_id - 1)
    yp1 = tl.where(y_id + 1 >= G, 2 * G - 1 - (y_id + 1), y_id + 1)
    ym2 = tl.where(y_id - 2 < 0, -1 - (y_id - 2), y_id - 2)
    yp2 = tl.where(y_id + 2 >= G, 2 * G - 1 - (y_id + 2), y_id + 2)

    zm1 = tl.where(offs_z - 1 < 0, -1 - (offs_z - 1), offs_z - 1)
    zp1 = tl.where(offs_z + 1 >= G, 2 * G - 1 - (offs_z + 1), offs_z + 1)
    zm2 = tl.where(offs_z - 2 < 0, -1 - (offs_z - 2), offs_z - 2)
    zp2 = tl.where(offs_z + 2 >= G, 2 * G - 1 - (offs_z + 2), offs_z + 2)

    c = tl.load(p_curr_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    pm = tl.load(p_prev_ptr + (x_id * G + y_id) * G + offs_z, mask=mask, other=0.0)
    # 6 face neighbors (1,0,0)
    pxp = tl.load(p_curr_ptr + (xp1 * G + y_id) * G + offs_z, mask=mask, other=0.0)
    pxm = tl.load(p_curr_ptr + (xm1 * G + y_id) * G + offs_z, mask=mask, other=0.0)
    pyp = tl.load(p_curr_ptr + (x_id * G + yp1) * G + offs_z, mask=mask, other=0.0)
    pym = tl.load(p_curr_ptr + (x_id * G + ym1) * G + offs_z, mask=mask, other=0.0)
    pzp = tl.load(p_curr_ptr + (x_id * G + y_id) * G + zp1, mask=mask, other=0.0)
    pzm = tl.load(p_curr_ptr + (x_id * G + y_id) * G + zm1, mask=mask, other=0.0)
    s_face = pxp + pxm + pyp + pym + pzp + pzm

    # 6 axial-2 neighbors (2,0,0)
    s_ax2 = (
        tl.load(p_curr_ptr + (xp2 * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm2 * G + y_id) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + yp2) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + ym2) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zp2, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + y_id) * G + zm2, mask=mask, other=0.0)
    )

    # 12 edge neighbors (1,1,0)
    s_edge = (
        tl.load(p_curr_ptr + (xp1 * G + yp1) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xp1 * G + ym1) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm1 * G + yp1) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm1 * G + ym1) * G + offs_z, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xp1 * G + y_id) * G + zp1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xp1 * G + y_id) * G + zm1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm1 * G + y_id) * G + zp1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (xm1 * G + y_id) * G + zm1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + yp1) * G + zp1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + yp1) * G + zm1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + ym1) * G + zp1, mask=mask, other=0.0)
        + tl.load(p_curr_ptr + (x_id * G + ym1) * G + zm1, mask=mask, other=0.0)
    )
    pn = w0 * c + w_face * s_face + w_ax2 * s_ax2 + w_edge * s_edge - pm
    tl.store(p_next_ptr + (x_id * G + y_id) * G + offs_z, pn, mask=mask)


def kspace_multiplier64(G: int, nu: float, device) -> torch.Tensor:
    """Exact leapfrog multiplier 2 cos(nu |k|) on the rfftn half spectrum of a periodic G^3 grid (float64)."""
    kf_full = 2.0 * math.pi * torch.fft.fftfreq(G, device=device, dtype=torch.float64)
    kf_r = 2.0 * math.pi * torch.fft.rfftfreq(G, device=device, dtype=torch.float64)
    kx_g, ky_g, kz_g = torch.meshgrid(kf_full, kf_full, kf_r, indexing="ij")
    return 2.0 * torch.cos(nu * torch.sqrt(kx_g**2 + ky_g**2 + kz_g**2))


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
        {"name": "13-pt O(dx^4,dt^2) FDTD (nu=0.50)", "kind": "fdtd13", "nu": 0.50, "inter": torch.float32},
        {"name": "27-pt IWB (nu=0.75)", "kind": "iwb27", "nu": 0.75, "inter": torch.float32},
        {"name": "27-pt IWB (nu=1.00)", "kind": "iwb27", "nu": 1.00, "inter": torch.float32},
        {"name": "25-pt O(dx^4,dt^4) FDTD (nu=1/sqrt3)", "kind": "fdtd25", "nu": 1.0 / math.sqrt(3.0), "inter": torch.float32},
        {"name": "k-space cuFFT (periodic, nu=1.00)", "kind": "kspace", "nu": 1.00, "inter": torch.float32},
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
            sep_step = gk.SeparableStep3D(prop["factors_exact"], prop["alpha0"], G, case["inter"])

        elif case["kind"] == "fdtd25":
            c1_25 = (8.0 / 3.0) * (nu**2) - 2.0 * (nu**4)
            c2_25 = ((nu**4) - (nu**2)) / 6.0
            c11_25 = (2.0 / 3.0) * (nu**4)
            w0_25 = 2.0 - 3.0 * (c1_25 + c2_25 + c11_25)
            wf_25 = 0.5 * c1_25
            wa_25 = 0.5 * c2_25
            we_25 = 0.25 * c11_25

        elif case["kind"] == "kspace":
            kspace_step = gk.KSpaceStep3D(kspace_multiplier64(G, nu, device))

        traces = {k: [float(p0_np[c_idx + dx, c_idx + dy, c_idx + dz]), float(p1_np[c_idx + dx, c_idx + dy, c_idx + dz])]
                  for k, (dx, dy, dz) in rec_offsets.items()}
        ct_times = [0.0, nu]

        grid_2d = (G * G, triton.cdiv(G, 256))
        if snap_step == 1 and case["name"] in {"7-pt FDTD (nu=1/sqrt3)", "27-pt IWB (nu=1.00)", "Rank-7 (2c+1r, nu=0.75)"}:
            snapshots[case["name"]] = p_curr[c_idx - 64 : c_idx + 65, c_idx - 64 : c_idx + 65, c_idx].cpu().numpy().tolist()

        for step in range(2, n_steps + 1):
            if case["kind"] == "fdtd7":
                fdtd7_triton_kernel[grid_2d](p_curr, p_prev, p_next, nu**2, G=G, BLOCK_Z=256)
            elif case["kind"] == "fdtd13":
                fdtd13_o4_triton_kernel[grid_2d](p_curr, p_prev, p_next, nu**2, G=G, BLOCK_Z=256)
            elif case["kind"] == "fdtd25":
                fdtd25_o4_triton_kernel[grid_2d](p_curr, p_prev, p_next, w0_25, wf_25, wa_25, we_25, G=G, BLOCK_Z=256)
            elif case["kind"] == "iwb27":
                iwb27_triton_kernel[grid_2d](p_curr, p_prev, p_next, nu**2, G=G, BLOCK_Z=256)
            elif case["kind"] == "kspace":
                kspace_step(p_curr, p_prev, p_next)
            else:
                sep_step(p_curr, p_prev, p_next)

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
    step = gk.SeparableStep3D(prop["factors_exact"], prop["alpha0"], G_room)

    # Off-center Gaussian initial condition in rigid room [0, 64)^3 -> excites all 3-D room modes!
    coords = torch.arange(G_room, device=device, dtype=torch.float32)
    xx, yy, zz = torch.meshgrid(coords, coords, coords, indexing="ij")
    r2 = (xx - 21.3) ** 2 + (yy - 29.7) ** 2 + (zz - 18.4) ** 2
    p_prev = torch.exp(-0.25 * r2)
    p_curr = torch.empty_like(p_prev)
    p_next = torch.empty_like(p_prev)

    # Symmetric first step for dp/dt(0) = 0: p^1 = 0.5 * (M * p^0)
    step(p_prev, torch.zeros_like(p_prev), p_curr)
    p_curr = 0.5 * p_curr

    def discrete_energy(pc, pp):
        # Apply M * pp via one step with zero prev -> M_pp
        M_pp = torch.empty_like(pc)
        step(pp, torch.zeros_like(pp), M_pp)
        diff_norm2 = torch.sum((pc - pp) ** 2).item()
        pot = torch.sum(pc * (2.0 * pp - M_pp)).item()
        return diff_norm2 + pot

    e_init = discrete_energy(p_curr, p_prev)
    for _ in range(2, n_steps + 1):
        step(p_curr, p_prev, p_next)
        p_prev, p_curr, p_next = p_curr, p_next, p_prev
    e_final = discrete_energy(p_curr, p_prev)
    rel_drift = abs(e_final - e_init) / abs(e_init)
    print(f"Rigid 64^3 Room ({n_steps} steps, >18 wall reflections) {prop['label']}: E_0={e_init:.6f}, E_{n_steps}={e_final:.6f}, rel drift={rel_drift:.2e}")
    assert rel_drift < 1e-4 and e_final > 0, f"Energy drift too large: {rel_drift}"
    return {"e_init": e_init, "e_final": e_final, "rel_drift": rel_drift}


def reference_step64(p_curr64, p_prev64, factors, alpha0: float):
    """
    float64 leapfrog step p_next = alpha0 p + sum_n (fx_n (x) fy_n (x) fz_n) * p - p_prev with half-sample
    reflecting (Neumann) walls, evaluated as plain index-shifted sums on the GPU.
    """
    G = p_curr64.shape[0]
    L = len(factors[0][0]) - 1
    idx = torch.arange(-L, G + L, device=p_curr64.device)
    idx = torch.where(idx < 0, -1 - idx, idx)
    idx = torch.where(idx >= G, 2 * G - 1 - idx, idx)

    def fir(u, half, axis):
        out = torch.zeros_like(u)
        for m in range(-L, L + 1):
            out += float(half[abs(m)]) * u.index_select(axis, idx[L + m: L + m + G])
        return out

    acc = alpha0 * p_curr64 - p_prev64
    for fx, fy, fz in factors:
        acc += fir(fir(fir(p_curr64, fz, 2), fy, 1), fx, 0)
    return acc


GPU_BENCHMARK_INFO = {
    "fields": "256^3 float32 p_curr and p_prev with independent uniform [-0.5, 0.5) samples (torch.Generator seed 0)",
    "errors": "err_max_* and err_rms_* are absolute errors of one leapfrog step against the same step in float64: "
              "separable and direct steps against shifted sums with half-sample reflecting walls, the k-space step "
              "against float64 rfftn/irfftn; the single-pass FDTD kernels are unchanged and not re-validated here",
    "timing": "mean and standard deviation in ms per step over 10 CUDA-Event batches (direct: 6 batches); "
              "launch parameters (config_*) are tuned by timing at start-up, and means differed by up to 3% "
              "between two complete runs, more than the within-run standard deviations",
    "direct": "Triton dense W^3 stencil step on a z-padded copy of p_curr, four x-planes per program",
    "kspace": "periodic cuFFT step split into L2-resident chunks (2-D real transforms per group of x-planes; x "
              "transform, spectral multiply and inverse x transform per group of y-rows)",
    "sep": "Triton x fan-out, y, and z fan-in + update passes over L2-resident slabs; fp16 stores the two slab "
           "intermediates in float16 (fields and accumulation stay float32)",
}


def benchmark_3d_gpu(propagators, G: int = 256):
    """
    Benchmark 256^3 step times on RTX 4070 Ti Super (10 CUDA-Event batches: mean +/- std) and measure the
    single-step error of the k-space, direct and separable steps against float64 (see GPU_BENCHMARK_INFO).
    """
    device = torch.device("cuda")
    gen = torch.Generator().manual_seed(0)
    p_curr64 = (torch.rand((G, G, G), generator=gen, dtype=torch.float64) - 0.5).to(device)
    p_prev64 = (torch.rand((G, G, G), generator=gen, dtype=torch.float64) - 0.5).to(device)
    p_curr = p_curr64.to(torch.float32)
    p_prev = p_prev64.to(torch.float32)
    p_next = torch.empty_like(p_curr)
    grid_2d = (G * G, triton.cdiv(G, 256))

    bench = []

    # 1. 7-pt FDTD
    ms7, std7 = gk.cuda_batch_stats(
        lambda: fdtd7_triton_kernel[grid_2d](p_curr, p_prev, p_next, 1.0 / 3.0, G=G, BLOCK_Z=256),
        warmup=10, n_batches=10, iters_per_batch=20,
    )
    bench.append({"name": "7-pt FDTD (1-pass Triton)", "W": 3, "rank": None, "ms_fp32": ms7, "ms_fp32_std": std7, "gvox_fp32": (G**3 / 1e9) / (ms7 / 1000.0)})
    print(f"Bench 256^3 7-pt FDTD (1-pass Triton): {ms7:.3f}+/-{std7:.3f} ms/step ({(G**3/1e9)/(ms7/1000.0):.2f} GVox/s)")

    # 1b. 13-pt O(dx^4, dt^2) axial FDTD
    ms13, std13 = gk.cuda_batch_stats(
        lambda: fdtd13_o4_triton_kernel[grid_2d](p_curr, p_prev, p_next, 0.25, G=G, BLOCK_Z=256),
        warmup=10, n_batches=10, iters_per_batch=20,
    )
    bench.append({"name": "13-pt O(dx^4,dt^2) FDTD (1-pass Triton)", "W": 5, "rank": None, "ms_fp32": ms13, "ms_fp32_std": std13, "gvox_fp32": (G**3 / 1e9) / (ms13 / 1000.0)})
    print(f"Bench 256^3 13-pt O(dx^4,dt^2) (1-pass Triton): {ms13:.3f}+/-{std13:.3f} ms/step ({(G**3/1e9)/(ms13/1000.0):.2f} GVox/s)")

    # 2. 27-pt IWB FDTD (dedicated 1-pass Triton)
    ms27, std27 = gk.cuda_batch_stats(
        lambda: iwb27_triton_kernel[grid_2d](p_curr, p_prev, p_next, 1.0, G=G, BLOCK_Z=256),
        warmup=10, n_batches=10, iters_per_batch=20,
    )
    bench.append({"name": "27-pt IWB (1-pass Triton)", "W": 3, "rank": 1, "ms_fp32": ms27, "ms_fp32_std": std27, "gvox_fp32": (G**3 / 1e9) / (ms27 / 1000.0)})
    print(f"Bench 256^3 27-pt IWB (1-pass Triton): {ms27:.3f}+/-{std27:.3f} ms/step ({(G**3/1e9)/(ms27/1000.0):.2f} GVox/s)")

    # 2a. 25-pt O(dx^4, dt^4) compact explicit FDTD (Hamilton & Bilbao 2016)
    nu25 = 1.0 / math.sqrt(3.0)
    c1_25 = (8.0 / 3.0) * (nu25**2) - 2.0 * (nu25**4)
    c2_25 = ((nu25**4) - (nu25**2)) / 6.0
    c11_25 = (2.0 / 3.0) * (nu25**4)
    w0_25 = 2.0 - 3.0 * (c1_25 + c2_25 + c11_25)
    ms25, std25 = gk.cuda_batch_stats(
        lambda: fdtd25_o4_triton_kernel[grid_2d](p_curr, p_prev, p_next, w0_25, 0.5 * c1_25, 0.5 * c2_25, 0.25 * c11_25, G=G, BLOCK_Z=256),
        warmup=10, n_batches=10, iters_per_batch=20,
    )
    bench.append({"name": "25-pt O(dx^4,dt^4) FDTD (1-pass Triton)", "W": 5, "rank": None, "ms_fp32": ms25, "ms_fp32_std": std25, "gvox_fp32": (G**3 / 1e9) / (ms25 / 1000.0)})
    print(f"Bench 256^3 25-pt O(dx^4,dt^4) (1-pass Triton): {ms25:.3f}+/-{std25:.3f} ms/step ({(G**3/1e9)/(ms25/1000.0):.2f} GVox/s)")

    # 2b. Periodic k-space pseudospectral baseline (exact nu = 1 multiplier, L2-chunked cuFFT)
    m_hat64 = kspace_multiplier64(G, 1.0, device)
    ref_k = torch.fft.irfftn(torch.fft.rfftn(p_curr64) * m_hat64, s=(G, G, G)) - p_prev64
    kstep = gk.KSpaceStep3D.tuned(m_hat64, p_curr, p_prev, p_next)
    p_next.zero_()
    ms_kspace, std_kspace = gk.cuda_batch_stats(lambda: kstep(p_curr, p_prev, p_next), warmup=10, n_batches=10, iters_per_batch=12)
    e_max, e_rms = gk.max_rms_error(p_next, ref_k)
    assert e_max < 2e-5, f"k-space step error {e_max}"
    bench.append({
        "name": "k-space cuFFT (periodic, L2-chunked)", "W": G, "rank": None, "ms_fp32": ms_kspace, "ms_fp32_std": std_kspace,
        "gvox_fp32": (G**3 / 1e9) / (ms_kspace / 1000.0), "err_max_fp32": e_max, "err_rms_fp32": e_rms, "config": kstep.config,
    })
    print(f"Bench 256^3 k-space cuFFT (periodic, L2-chunked): {ms_kspace:.3f}+/-{std_kspace:.3f} ms/step ({(G**3/1e9)/(ms_kspace/1000.0):.2f} GVox/s, err {e_max:.1e})")
    del kstep, ref_k, m_hat64

    # 3. Direct W^3 stencil vs Naive vs Exact separable (fp32 & fp16-inter) for each unique (L, rank_exact, rank_naive)
    seen = set()
    for prop in propagators:
        key = (prop["L"], prop["rank_exact"], prop["rank_naive"])
        if key in seen:
            continue
        seen.add(key)
        L = prop["L"]
        W = prop["W"]
        alpha0 = prop["alpha0"]
        if "factors_naive" in prop:
            raw_ex, raw_nv = prop["factors_exact"], prop["factors_naive"]
        else:
            raw_ex, raw_nv = build_3d_separable_factors(L, prop["components"])
        ref = reference_step64(p_curr64, p_prev64, raw_ex, alpha0)

        row = {"label": prop["label"], "L": L, "W": W, "rank_exact": prop["rank_exact"], "rank_naive": prop["rank_naive"]}

        def measure(step, name, batches, iters, reference, tol):
            p_next.zero_()
            ms, std = gk.cuda_batch_stats(lambda: step(p_curr, p_prev, p_next), warmup=4, n_batches=batches, iters_per_batch=iters)
            e_max, e_rms = gk.max_rms_error(p_next, reference)
            assert e_max < tol, f"{name} step error {e_max} for {prop['label']}"
            row.update({f"ms_{name}": ms, f"ms_{name}_std": std, f"err_max_{name}": e_max, f"err_rms_{name}": e_rms,
                        f"config_{name}": step.config})

        idx_full = np.abs(np.arange(-L, L + 1))
        stencil = sum(np.einsum("i,j,k->ijk", fx[idx_full], fy[idx_full], fz[idx_full]) for fx, fy, fz in raw_ex)
        stencil[L, L, L] += alpha0
        measure(gk.DirectStep3D.tuned(stencil, p_curr, p_prev, p_next), "direct_fp32", 6, 4, ref, 5e-5)
        measure(gk.SeparableStep3D.tuned(raw_nv, alpha0, p_curr, p_prev, p_next), "naive_fp32", 10, 8,
                reference_step64(p_curr64, p_prev64, raw_nv, alpha0), 2e-5)
        measure(gk.SeparableStep3D.tuned(raw_ex, alpha0, p_curr, p_prev, p_next), "exact_fp32", 10, 8, ref, 2e-5)
        measure(gk.SeparableStep3D.tuned(raw_ex, alpha0, p_curr, p_prev, p_next, torch.float16), "exact_fp16", 10, 8, ref, 2e-2)
        row["gvox_exact_fp32"] = (G**3 / 1e9) / (row["ms_exact_fp32"] / 1000.0)
        row["gvox_exact_fp16"] = (G**3 / 1e9) / (row["ms_exact_fp16"] / 1000.0)
        bench.append(row)
        print(
            f"Bench 256^3 W={W:2d} (R={prop['rank_exact']} vs naive {prop['rank_naive']}): "
            f"Direct={row['ms_direct_fp32']:6.2f}+/-{row['ms_direct_fp32_std']:.2f} ms (err {row['err_max_direct_fp32']:.1e}) | "
            f"Naive={row['ms_naive_fp32']:5.2f}+/-{row['ms_naive_fp32_std']:.3f} ms (err {row['err_max_naive_fp32']:.1e}) | "
            f"Exact fp32={row['ms_exact_fp32']:5.2f}+/-{row['ms_exact_fp32_std']:.3f} ms (err {row['err_max_exact_fp32']:.1e}) | "
            f"Exact fp16={row['ms_exact_fp16']:5.2f}+/-{row['ms_exact_fp16_std']:.3f} ms (err {row['err_max_exact_fp16']:.1e})"
        )
    return bench


def benchmark_3d_cpu(G: int = 128, L: int = 6, R: int = 7):
    """Multi-core CPU reference timings on 128^3 voxels (Intel Core Ultra 5 125H, float32, 4 runs: mean +/- std)."""
    W = 2 * L + 1
    p_c = torch.randn((1, 1, G, G, G), dtype=torch.float32)
    p_p = torch.randn((1, 1, G, G, G), dtype=torch.float32)
    m_hat = torch.randn((G, G, G // 2 + 1), dtype=torch.float32)

    def _stats(fn, n_runs: int = 4):
        fn()
        ts = []
        for _ in range(n_runs):
            t0 = time.perf_counter()
            fn()
            ts.append(1000.0 * (time.perf_counter() - t0))
        arr = np.array(ts, dtype=np.float64)
        return float(np.mean(arr)), float(np.std(arr, ddof=1))

    # 1. k-space periodic rfftn/irfftn
    ms_fft, std_fft = _stats(lambda: torch.fft.irfftn(torch.fft.rfftn(p_c[0, 0]) * m_hat, s=(G, G, G)) - p_p[0, 0])

    # 2. Separable R=7 1-D conv3d cascade vs naive R=9
    kx = [torch.randn((1, 1, W, 1, 1), dtype=torch.float32) for _ in range(9)]
    ky = [torch.randn((1, 1, 1, W, 1), dtype=torch.float32) for _ in range(9)]
    kz = [torch.randn((1, 1, 1, 1, W), dtype=torch.float32) for _ in range(9)]

    def _run_sep(n_terms):
        acc = None
        for r in range(n_terms):
            u = F.conv3d(F.pad(p_c, (L, L, 0, 0, 0, 0), mode="replicate"), kz[r])
            v = F.conv3d(F.pad(u, (0, 0, L, L, 0, 0), mode="replicate"), ky[r])
            w = F.conv3d(F.pad(v, (0, 0, 0, 0, L, L), mode="replicate"), kx[r])
            acc = w if acc is None else (acc + w)
        return acc - p_p

    ms_sep7, std_sep7 = _stats(lambda: _run_sep(R))
    ms_sep9, std_sep9 = _stats(lambda: _run_sep(9))

    # 3. Direct 13^3 conv3d (1 warmup + 2 timed runs because 13^3 on 128^3 CPU is ~O(seconds))
    k3d = torch.randn((1, 1, W, W, W), dtype=torch.float32)
    ms_dir, std_dir = _stats(lambda: F.conv3d(F.pad(p_c, (L,) * 6, mode="replicate"), k3d) - p_p, n_runs=2)
    # Also measure 256^3 k-space FFT on CPU (DRAM-resident, direct comparison with 256^3 GPU!)
    p256 = torch.randn((256, 256, 256), dtype=torch.float32)
    q256 = torch.randn((256, 256, 256), dtype=torch.float32)
    m256 = torch.randn((256, 256, 129), dtype=torch.float32)
    ms_fft256, std_fft256 = _stats(lambda: torch.fft.irfftn(torch.fft.rfftn(p256) * m256, s=(256, 256, 256)) - q256, n_runs=4)

    out = {
        "grid": G,
        "W": W,
        "ms_kspace_fp32": ms_fft, "ms_kspace_fp32_std": std_fft,
        "ms_kspace_256cubed_fp32": ms_fft256, "ms_kspace_256cubed_fp32_std": std_fft256,
        "ms_sep_R7_fp32": ms_sep7, "ms_sep_R7_fp32_std": std_sep7,
        "ms_sep_R9_naive_fp32": ms_sep9, "ms_sep_R9_naive_fp32_std": std_sep9,
        "ms_direct_13cubed_fp32": ms_dir, "ms_direct_13cubed_fp32_std": std_dir,
    }
    print(
        f"CPU {G}^3 (W={W}): k-space={ms_fft:.1f}+/-{std_fft:.1f} ms | "
        f"Sep R=7={ms_sep7:.1f}+/-{std_sep7:.1f} ms (Naive R=9={ms_sep9:.1f} ms) | Direct {W}^3={ms_dir:.1f} ms"
    )
    return out


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
        ("25-pt O(dx^4,dt^4) FDTD (nu=1/sqrt3)", "fdtd_25pt_o4", 1.0 / math.sqrt(3.0)),
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


RESULTS_PATH = os.path.join(os.path.dirname(__file__), "results_acoustics_3d.json")


def run_gpu_experiments(propagators):
    """Wave simulation, rigid-room energy test and throughput benchmarks, keyed as in the results file."""
    print("\n=== 3-D Broadband Spherical Wave Simulation on 256^3 Grid (RTX 4070 Ti Super) ===")
    sim_results, snapshots = run_3d_spherical_wave_experiment(propagators, G=256, ct_max=72.0, sigma0=1.40)

    print("\n=== 1,000-Step Rigid 3-D Room Neumann Wall Energy Conservation ===")
    room_checks = {}
    for prop in propagators:
        if prop["label"] in {"Rank-7 (2c+1r, nu=0.75)", "Rank-7 (2c+1r, nu=1.00)", "Rank-7 (deg1 1c, nu=0.75)"}:
            room_checks[prop["label"]] = verify_rigid_room_long_time_stability(prop, G_room=64, n_steps=1000)

    print("\n=== Hardware-Fair RTX 4070 Ti Super 256^3 Throughput Benchmarks ===")
    gpu_bench = benchmark_3d_gpu(propagators, G=256)
    return {
        "spherical_wave_sim": sim_results,
        "snapshots_z0_ct48": snapshots,
        "rigid_room_energy": room_checks,
        "gpu_benchmark_256cubed": gpu_bench,
        "gpu_benchmark_info": GPU_BENCHMARK_INFO,
    }


def rerun_gpu_experiments():
    """Rerun only the GPU parts from the stored propagators and update the stored results."""
    with open(RESULTS_PATH, encoding="utf-8") as f:
        results = json.load(f)
    propagators = []
    for stored in results["propagators"]:
        prop = dict(stored)
        prop["factors_exact"], prop["factors_naive"] = build_3d_separable_factors(prop["L"], prop["components"])
        for tup, tup_stored in zip(prop["factors_exact"], stored["factors_exact"]):
            assert np.allclose(np.array(tup), np.array(tup_stored), rtol=1e-12, atol=1e-15), prop["label"]
        propagators.append(prop)
    results.update(run_gpu_experiments(propagators))
    with open(RESULTS_PATH, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2)
    print(f"\nUpdated GPU results in {RESULTS_PATH}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--gpu-only", action="store_true", help="rerun only the GPU simulation, room test and benchmarks")
    if parser.parse_args().gpu_only:
        return rerun_gpu_experiments()

    verify_iwb_is_single_real_gaussian()

    K_oct, kmag_oct, _ = build_octant_grid(65, k_cut_frac=0.80)
    print(f"Built 65^3 Brillouin octant certification grid: {K_oct.shape[0]} unique symmetry-inequivalent 3-D wavevectors.")

    u_dirs = build_octant_unit_dirs(16)
    baselines = []
    for name, sch, nu in [
        ("7-pt FDTD (nu=1/sqrt3)", "fdtd_7pt", 1.0 / math.sqrt(3.0)),
        ("13-pt O(dx^4,dt^2) FDTD (nu=0.50)", "fdtd_13pt_o4", 0.50),
        ("27-pt IWB (nu=0.75)", "iwb_27pt", 0.75),
        ("27-pt IWB (nu=1.00)", "iwb_27pt", 1.00),
        ("25-pt O(dx^4,dt^4) FDTD (nu=1/sqrt3)", "fdtd_25pt_o4", 1.0 / math.sqrt(3.0)),
    ]:
        eval_b = lambda K_q, s=sch, n=nu: evaluate_baseline_octant(s, n, K_q, np.linalg.norm(K_q, axis=1))
        M_b = evaluate_baseline_octant(sch, nu, K_oct, kmag_oct)
        bw01 = effective_bandwidth_frac_fn(eval_b, nu, tol=1e-3, u_dirs=u_dirs)
        bw05 = effective_bandwidth_frac_fn(eval_b, nu, tol=5e-3, u_dirs=u_dirs)
        in75 = kmag_oct <= 0.75 * np.pi + 1e-12
        in80 = kmag_oct <= 0.80 * np.pi + 1e-12
        err75_g = np.abs(np.arccos(np.clip(M_b[in75] / 2.0, -1.0, 1.0)) / (nu * kmag_oct[in75]) - 1.0)
        err80_g = np.abs(np.arccos(np.clip(M_b[in80] / 2.0, -1.0, 1.0)) / (nu * kmag_oct[in80]) - 1.0)
        err75 = continuous_refine_max_pv_err(eval_b, K_oct[in75], err75_g, nu, 0.75 * np.pi)
        err80 = continuous_refine_max_pv_err(eval_b, K_oct[in80], err80_g, nu, 0.80 * np.pi)
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

    gpu_results = run_gpu_experiments(propagators)
    cpu_bench = benchmark_3d_cpu(G=128, L=6, R=7)
    disp_curves = compute_dispersion_curves(propagators)

    # Strip numpy arrays inside factors for clean JSON serialization
    serializable_props = []
    for p in propagators:
        p_copy = {k: v for k, v in p.items() if k not in {"factors_exact", "factors_naive"}}
        p_copy["factors_exact"] = [[f.tolist() for f in tup] for tup in p["factors_exact"]]
        serializable_props.append(p_copy)

    out_path = RESULTS_PATH
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "baselines": baselines,
                "propagators": serializable_props,
                **gpu_results,
                "cpu_benchmark_128cubed": cpu_bench,
                "dispersion_curves": disp_curves,
            },
            f,
            indent=2,
        )
    print(f"\nSaved 3-D acoustic simulation results to {out_path}")


if __name__ == "__main__":
    main()
