"""
Generate publication-quality vector PDF figures for `paper/main.tex` from
`Applications/results_blur_2d.json` and `Applications/results_acoustics_3d.json`.
"""
import json
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def configure_style():
    plt.rcParams.update({
        "font.family": "serif",
        "font.size": 9.5,
        "axes.titlesize": 10.0,
        "axes.labelsize": 9.5,
        "legend.fontsize": 8.0,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "axes.linewidth": 0.8,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })


def make_blur_2d_figure(app_dir: str, paper_dir: str, preview_dir: str | None = None):
    with open(os.path.join(app_dir, "results_blur_2d.json"), "r", encoding="utf-8") as f:
        data = json.load(f)

    fig, axes = plt.subplots(1, 3, figsize=(13.2, 3.65), constrained_layout=True)

    # --- Panel (a): Radial profiles vs ideal disc ---
    ax = axes[0]
    r = np.array(data["profile_curves"]["r"])
    ideal = (r <= 1.0).astype(float)
    ax.axvspan(1.0, 1.2, color="#e8ecf2", alpha=0.9, label=r"Transition $[1, 1.2]$")
    ax.axvline(1.2 * np.sqrt(2.0), color="#888888", ls=":", lw=1.0)
    ax.text(1.2 * np.sqrt(2.0) - 0.03, 1.18, r"2-D corner $\sqrt{2}S$", ha="right", va="top", fontsize=7.8, color="#555555")
    ax.plot(r, ideal, color="#222222", lw=1.3, ls="--", label="Target disc")

    curve_styles = [
        ("1r_4 (deg 3 real)", "#8c564b", "-.", 1.2, r"Real poly $1r_4$ ($N{=}4$)"),
        ("1c (Gaussian)", "#ff7f0e", "-", 1.2, r"Complex $1c$ ($N{=}2$)"),
        ("1c+1r", "#2ca02c", "-", 1.25, r"Mixed $1c{+}1r$ ($N{=}3$)"),
        ("2c (Gaussian)", "#1f77b4", "-", 1.4, r"Complex $2c$ ($N{=}4$)"),
        ("6c (Gaussian)", "#d62728", "-", 1.5, r"Complex $6c$ ($N{=}12$)"),
    ]
    for key, col, ls, lw, lbl in curve_styles:
        ax.plot(r, data["profile_curves"][key], color=col, ls=ls, lw=lw, label=lbl)

    ax.set_xlim(0.0, 1.80)
    ax.set_ylim(-0.28, 1.26)
    ax.set_xlabel(r"Normalized radius $r = \sqrt{x^2 + y^2}$")
    ax.set_ylabel(r"Radial profile $\varphi(r^2)$")
    ax.set_title("(a) 2-D circular disc-blur profiles ($\\tau = 0.2$)")
    ax.grid(True, alpha=0.25, lw=0.5)
    ax.legend(loc="lower left", frameon=True, framealpha=0.93, fontsize=7.3)

    # --- Panel (b): Minimax ripple vs exact 2-D separable rank N ---
    ax = axes[1]
    fams = data["families"]

    def extract_xy(grp):
        pts = sorted([(f["rank_2d"], f["ripple_2d"], f) for f in fams if f["kind_group"] == grp], key=lambda t: t[0])
        return [p[0] for p in pts], [p[1] for p in pts], [p[2] for p in pts]

    x_cg, y_cg, _ = extract_xy("complex_gaussian")
    x_mg, y_mg, _ = extract_xy("mixed_gaussian")
    x_cp, y_cp, _ = extract_xy("complex_poly")
    x_rp, y_rp, _ = extract_xy("real_poly")

    ax.semilogy(x_rp, y_rp, "s--", color="#8c564b", lw=1.3, ms=5.2, label=r"Single real rate $1r_m$ ($\deg{=}m{-}1$)")
    ax.semilogy(x_cp, y_cp, "^--", color="#9467bd", lw=1.3, ms=5.5, label=r"Single complex rate $1c_m$ ($\deg{=}m{-}1$)")
    ax.semilogy(x_cg, y_cg, "o-", color="#1f77b4", lw=1.6, ms=5.6, label=r"Distinct complex Gaussians ($c{=}1\dots 6$)")
    ax.semilogy(x_mg, y_mg, "D", color="#2ca02c", ms=5.8, label=r"Odd-rank mixed ($c$ complex + $1$ real)")

    # Also plot 1c+1r_2 at N=4
    mp = [f for f in fams if f["kind_group"] == "mixed_poly"][0]
    ax.semilogy([mp["rank_2d"]], [mp["ripple_2d"]], "P", color="#17becf", ms=6.8, label=r"Mixed $1c + 1r_2$ ($N{=}4, R_3{=}6$)")

    ax.annotate(
        r"$N{=}4$: $2c$ ($R_3{=}6$)" "\n" r"beats $1c_2$ ($R_3{=}7$)",
        xy=(4, 0.07593), xytext=(5.5, 0.16),
        arrowprops={"arrowstyle": "->", "lw": 0.8, "color": "#333333"},
        fontsize=7.6, bbox={"boxstyle": "round,pad=0.2", "fc": "#f8f9fa", "ec": "#cccccc", "lw": 0.6},
    )

    ax.set_xticks(range(2, 13))
    ax.set_ylim(1.2e-3, 0.5)
    ax.set_xlabel(r"Exact 2-way real separable rank $N$")
    ax.set_ylabel(r"Minimax pass/stopband ripple $\max |\varphi - \mathbf{1}_{r \leq 1}|$")
    ax.set_title("(b) Minimax ripple vs. exact rank $N$")
    ax.grid(True, which="both", alpha=0.25, lw=0.5)
    ax.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.3)

    # --- Panel (c): Conditioning & float16 bokeh error ---
    ax = axes[2]
    cond = data["conditioning"]
    cg_cond = sorted([c for c in cond if c["kind_group"] == "complex_gaussian"], key=lambda c: c["rank_2d"])
    cp_cond = sorted([c for c in cond if c["kind_group"] == "complex_poly"], key=lambda c: c["rank_2d"])

    ax.semilogy(
        [c["rank_2d"] for c in cg_cond], [c["fp16_max_raw_255"] for c in cg_cond],
        "o--", color="#d62728", lw=1.4, ms=5.2, label="Per-comp. ($c$ Gaussians)",
    )
    ax.semilogy(
        [c["rank_2d"] for c in cp_cond], [c["fp16_max_raw_255"] for c in cp_cond],
        "^--", color="#ff7f0e", lw=1.3, ms=5.2, label=r"Per-comp. ($1c_m$ poly)",
    )
    ax.semilogy(
        [c["rank_2d"] for c in cg_cond], [c["fp16_max_orth_255"] for c in cg_cond],
        "o-", color="#1f77b4", lw=1.6, ms=5.4, label=r"Orthog. $\mathrm{rowSpan}$ ($c$ Gauss.)",
    )
    ax.semilogy(
        [c["rank_2d"] for c in cp_cond], [c["fp16_max_orth_255"] for c in cp_cond],
        "^-", color="#2ca02c", lw=1.3, ms=5.0, label=r"Orthog. $\mathrm{rowSpan}$ ($1c_m$ poly)",
    )
    ax.axhline(1.0, color="#444444", ls=":", lw=1.0, label="1.0 / 255 (8-bit LSB)")

    ax.annotate(
        r"Amp $1110\times \to 2.32\times$" "\n" r"($6.79 \to 0.16 / 255$)",
        xy=(12, cp_cond[-1]["fp16_max_raw_255"]), xytext=(7.8, 7.6),
        arrowprops={"arrowstyle": "->", "lw": 0.8, "color": "#444444"},
        fontsize=7.3, bbox={"boxstyle": "round,pad=0.2", "fc": "#fff8f6", "ec": "#ddbbaa", "lw": 0.6},
    )

    ax.set_xticks([2, 4, 6, 8, 10, 12])
    ax.set_ylim(0.08, 19.0)
    ax.set_xlabel(r"Exact 2-way real separable rank $N$")
    ax.set_ylabel("Max float16 bokeh error (8-bit levels / 255)")
    ax.set_title(r"(c) $\mathrm{GL}_N(\mathbb{R})$ rebalancing & float16 error")
    ax.grid(True, which="both", alpha=0.25, lw=0.5)
    ax.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.0)

    pdf_path = os.path.join(paper_dir, "fig_blur_2d.pdf")
    fig.savefig(pdf_path)
    if preview_dir:
        fig.savefig(os.path.join(preview_dir, "fig_blur_2d.png"), dpi=200)
    plt.close(fig)
    print(f"Wrote {pdf_path}")


def make_acoustics_3d_figure(app_dir: str, paper_dir: str, preview_dir: str | None = None):
    with open(os.path.join(app_dir, "results_acoustics_3d.json"), "r", encoding="utf-8") as f:
        data = json.load(f)

    fig = plt.figure(figsize=(13.2, 6.7), constrained_layout=True)
    gs = fig.add_gridspec(2, 6, height_ratios=[1.05, 1.0])

    # --- Top-left (spans 3 cols): Directional phase-velocity dispersion ---
    ax_disp = fig.add_subplot(gs[0, :3])
    k_pi = np.array(data["dispersion_curves"]["k_over_pi"])
    models = data["dispersion_curves"]["models"]

    dir_ls = {"axis": "-", "face": "--", "body": ":"}
    scheme_specs = [
        ("7-pt FDTD (nu=1/sqrt3)", "#d62728", r"7-pt FDTD ($\nu{=}1/\sqrt{3}$)"),
        ("27-pt IWB (nu=1.00)", "#ff7f0e", r"27-pt IWB ($\nu{=}1, R{=}1$ real Gauss.)"),
        ("Rank-7 (2c+1r, nu=1.00)", "#1f77b4", r"Rank-7 ($2c{+}1r, \nu{=}1.00, W{=}13$)"),
    ]
    for mkey, col, mlbl in scheme_specs:
        for dkey, ls in dir_ls.items():
            lbl = f"{mlbl}" if dkey == "axis" else None
            ax_disp.plot(k_pi, models[mkey][dkey], color=col, ls=ls, lw=1.45 if dkey == "axis" else 1.25, label=lbl)

    # Dummy legend entries for ray directions
    ax_disp.plot([], [], color="#555555", ls="-", lw=1.2, label="Axis $(1,0,0)$")
    ax_disp.plot([], [], color="#555555", ls="--", lw=1.2, label="Face diag $(1,1,0)$")
    ax_disp.plot([], [], color="#555555", ls=":", lw=1.2, label="Body diag $(1,1,1)$")

    ax_disp.axvline(0.80, color="#888888", ls=":", lw=0.9)
    ax_disp.set_xlim(0.0, 0.86)
    ax_disp.set_ylim(-23.0, 2.2)
    ax_disp.set_xlabel(r"Normalized wavenumber $\|\mathbf{k}\|_2 / \pi$ (Nyquist $= 1$)")
    ax_disp.set_ylabel(r"Phase-velocity error $(c_{\mathrm{num}}/c_0 - 1)$ [%]")
    ax_disp.set_title("(a) 3-D directional acoustic phase-velocity dispersion")
    ax_disp.grid(True, alpha=0.25, lw=0.5)
    ax_disp.legend(loc="lower left", ncol=2, frameon=True, framealpha=0.93, fontsize=7.2)

    # Inset zoom placed in the unobstructed lower-middle region above the legend!
    ax_in = ax_disp.inset_axes([0.07, 0.31, 0.46, 0.45])
    ax_in.axhspan(-0.10, 0.10, color="#e8f4ea", alpha=0.85)
    for mkey, col, short in [
        ("Rank-7 (deg1 1c, nu=0.75)", "#9467bd", r"$R{=}7$ ($\deg 1, 1c$)"),
        ("Rank-6 (2c, nu=0.75)", "#2ca02c", r"$R{=}6$ ($2c$)"),
        ("Rank-7 (2c+1r, nu=1.00)", "#1f77b4", r"$R{=}7$ ($2c{+}1r, \nu{=}1$)"),
    ]:
        mask_z = k_pi <= (0.80 if "2c+1r" in mkey else 0.75)
        ax_in.plot(k_pi[mask_z], np.array(models[mkey]["axis"])[mask_z], color=col, ls="-", lw=1.1, label=short)
        ax_in.plot(k_pi[mask_z], np.array(models[mkey]["body"])[mask_z], color=col, ls=":", lw=1.0)
    ax_in.set_xlim(0.0, 0.82)
    ax_in.set_ylim(-0.18, 0.18)
    ax_in.set_title(r"Zoom ($\pm 0.10\%$ shaded)", fontsize=7.4, pad=2)
    ax_in.tick_params(labelsize=6.8)
    ax_in.grid(True, alpha=0.25, lw=0.4)
    ax_in.legend(loc="lower left", fontsize=6.2, frameon=True, framealpha=0.9)

    # --- Top-right (spans 3 cols): 3-D broadband receiver waveforms at face diagonal (34, 34, 0), r = 48.08 ---
    ax_wf = fig.add_subplot(gs[0, 3:])
    sims = {s["name"]: s for s in data["spherical_wave_sim"] if s["traces"] is not None}

    s_ref = sims["Rank-7 (2c+1r, nu=1.00)"]
    ct_ref = np.array(s_ref["ct"])
    # Continuous exact 3-D D'Alembert reference curve at r = sqrt(34^2 + 34^2)
    r_fd = np.hypot(34.0, 34.0)
    ct_dense = np.linspace(38.0, 68.0, 600)
    sigma0 = 1.40
    def f0_pulse(u):
        u2 = u**2
        return (1.0 - u2 / (sigma0**2)) * np.exp(-0.5 * u2 / (sigma0**2))
    ex_dense = ((r_fd - ct_dense) * f0_pulse(r_fd - ct_dense) + (r_fd + ct_dense) * f0_pulse(r_fd + ct_dense)) / (2.0 * r_fd)

    s_7pt = sims["7-pt FDTD (nu=1/sqrt3)"]
    s_iwb = sims["27-pt IWB (nu=1.00)"]
    s_r7_075 = sims["Rank-7 (2c+1r, nu=0.75)"]

    ax_wf.plot(ct_dense, ex_dense, color="#111111", lw=1.9, label=r"Exact 3-D D'Alembert ($r = 48.08\,\Delta x$)")
    ax_wf.plot(s_7pt["ct"], s_7pt["traces"]["face_diag"], color="#d62728", lw=1.1, alpha=0.9, label=r"7-pt FDTD (rel $L^2 = 109.3\%$)")
    ax_wf.plot(s_iwb["ct"], s_iwb["traces"]["face_diag"], color="#ff7f0e", lw=1.15, ls="--", alpha=0.95, label=r"27-pt IWB $\nu{=}1$ (rel $L^2 = 98.2\%$)")
    ax_wf.plot(s_r7_075["ct"], s_r7_075["traces"]["face_diag"], "o-", color="#2ca02c", lw=1.0, ms=2.6, alpha=0.9, label=r"Rank-7 $2c{+}1r, \nu{=}0.75$ (rel $L^2 = 2.8\%$)")
    ax_wf.plot(ct_ref, s_ref["traces"]["face_diag"], "s:", color="#1f77b4", lw=1.1, ms=3.0, label=r"Rank-7 $2c{+}1r, \nu{=}1.00$ (rel $L^2 = 2.0\%$)")

    ax_wf.set_xlim(38.0, 68.0)
    ax_wf.set_xlabel(r"Propagation distance $c_0 t / \Delta x$ [grid cells]")
    ax_wf.set_ylabel(r"Pressure $p(\mathbf{x}_{\mathrm{fd}}, t)$")
    ax_wf.set_title(r"(b) Broadband pulse waveforms at face-diagonal receiver $(34, 34, 0)$")
    ax_wf.grid(True, alpha=0.25, lw=0.5)
    ax_wf.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.4)

    # --- Bottom row: 3 mid-plane wavefield snapshots z = 0 at c0*t = 48 dx ---
    snaps = data["snapshots_z0_ct48"]
    snap_list = [
        ("7-pt FDTD (nu=1/sqrt3)", r"(c) 7-pt FDTD ($z{=}0$ slice, $c_0 t \approx 48\Delta x$)"),
        ("27-pt IWB (nu=1.00)", r"(d) 27-pt IWB ($\nu{=}1$, $R{=}1$ real Gaussian)"),
        ("Rank-7 (2c+1r, nu=0.75)", r"(e) Rank-7 multi-Gaussian ($2c{+}1r, W{=}13$)"),
    ]
    arr_ref = np.array(snaps["Rank-7 (2c+1r, nu=0.75)"])
    vmax = 0.85 * float(np.max(np.abs(arr_ref)))
    extent = [-64, 64, -64, 64]
    theta = np.linspace(0, 2 * np.pi, 300)

    im = None
    for idx_s, (skey, stitle) in enumerate(snap_list):
        ax_s = fig.add_subplot(gs[1, 2 * idx_s : 2 * idx_s + 2])
        arr = np.array(snaps[skey])
        im = ax_s.imshow(arr.T, origin="lower", extent=extent, cmap="RdBu_r", vmin=-vmax, vmax=vmax, interpolation="bilinear")
        ax_s.plot(48.0 * np.cos(theta), 48.0 * np.sin(theta), color="#222222", ls=":", lw=0.9, alpha=0.7)
        ax_s.set_title(stitle, fontsize=9.3)
        ax_s.set_xlabel(r"$x / \Delta x$")
        if idx_s == 0:
            ax_s.set_ylabel(r"$y / \Delta x$")
        else:
            ax_s.set_yticklabels([])
        ax_s.set_xticks([-48, -24, 0, 24, 48])
        ax_s.set_yticks([-48, -24, 0, 24, 48])

    fig.colorbar(im, ax=fig.axes[3:], shrink=0.86, pad=0.015, label=r"Pressure $p(x, y, 0, t)$")

    pdf_path = os.path.join(paper_dir, "fig_acoustics_3d.pdf")
    fig.savefig(pdf_path)
    if preview_dir:
        fig.savefig(os.path.join(preview_dir, "fig_acoustics_3d.png"), dpi=200)
    plt.close(fig)
    print(f"Wrote {pdf_path}")


def main():
    configure_style()
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    app_dir = os.path.join(repo_root, "Applications")
    paper_dir = os.path.join(repo_root, "paper")
    preview_dir = os.path.join(repo_root, ".tmp")
    make_blur_2d_figure(app_dir, paper_dir, preview_dir=preview_dir)
    make_acoustics_3d_figure(app_dir, paper_dir, preview_dir=preview_dir)


if __name__ == "__main__":
    main()
