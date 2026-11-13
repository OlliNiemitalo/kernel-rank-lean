"""
Generate publication-quality vector PDF figures for `paper/main.tex` from
`Applications/results_blur_2d.json` and `Applications/results_acoustics_3d.json`.
"""
import json
import math
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.patches import FancyBboxPatch
import numpy as np
from scipy.ndimage import convolve1d

from blur_2d import orthogonal_rowspan_channels_1d, per_component_channels_1d


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


def make_overview_pipeline_figure(app_dir: str, paper_dir: str, preview_dir: str | None = None):
    """
    Pedagogical Figure 1 (Section 1.1):
      (a) Mathematical "Components" view for 2c (N = 4): 1-D strips h(x) x v(y) -> 2-D outer products -> circular u_1, u_2 -> K.
      (b) Computational "Rendering terms" view: orthogonalized rowSpan terms t_1..t_4 (smallest first) -> K.
      (c) Step-by-step 2-pass image convolution showing the single overwritten horizontal intermediate buffer m <- I *_x h_n,
          the vertical pass output m *_y v_n, and the running accumulator A_1 -> A_2 -> A_3 -> A_4 -> rendered bokeh output.
    """
    with open(os.path.join(app_dir, "results_blur_2d.json"), "r", encoding="utf-8") as f:
        data = json.load(f)

    fam_2c = [fam for fam in data["families"] if fam["label"] == "2c (Gaussian)"][0]
    # Order components so u_1 is the wide low-frequency dome (c ~ 1.56) and u_2 is the higher-frequency ring (c ~ 5.27)
    comps = sorted(fam_2c["components"], key=lambda c: c["c"])

    # Custom perceptual signed colormap on white paper: crimson (-) <-> off-white (0) <-> deep navy-blue (+)
    signed_cmap = LinearSegmentedColormap.from_list(
        "signed_rb",
        [(0.0, "#b81d24"), (0.28, "#ef8a62"), (0.5, "#f7f8fa"), (0.72, "#67a9cf"), (1.0, "#124982")],
    )

    def signed_display(arr: np.ndarray, peak: float | None = None, gamma: float = 0.75):
        pk = float(np.max(np.abs(arr))) if peak is None else peak
        if pk < 1e-15:
            return np.zeros_like(arr), 0.0
        normed = np.clip(arr / pk, -1.0, 1.0)
        curved = np.sign(normed) * (np.abs(normed) ** gamma)
        return curved, pk

    # Dense 1-D grid on [-S, S] (S = 1.2) for clean kernel tiles in Panels (a) and (b)
    S = 1.2
    n_k = 81
    xk = np.linspace(-S, S, n_k)
    H_raw, V_raw = per_component_channels_1d(xk, comps, S=S)
    H_orth, V_orth = orthogonal_rowspan_channels_1d(H_raw, V_raw)

    fig = plt.figure(figsize=(13.2, 8.20))
    aspect = 13.2 / 8.20

    # Helper to draw a small image box in figure coordinates [x0, y0, w, h]
    def add_box_ax(rect):
        ax = fig.add_axes(rect)
        ax.set_xticks([])
        ax.set_yticks([])
        for sp in ax.spines.values():
            sp.set_linewidth(0.6)
            sp.set_edgecolor("#777f8c")
        return ax

    def draw_1d_hstrip(rect, vec: np.ndarray):
        ax = add_box_ax(rect)
        disp, _ = signed_display(vec, gamma=0.78)
        ax.imshow(disp[None, :], aspect="auto", cmap=signed_cmap, vmin=-1.0, vmax=1.0, extent=[0, 1, -1, 1])
        ax.axhline(0.0, color="#666666", lw=0.4, alpha=0.6)
        v_norm = vec / (np.max(np.abs(vec)) + 1e-15)
        ax.plot(np.linspace(0, 1, len(vec)), 0.78 * v_norm, color="#111111", lw=0.9)
        ax.set_xlim(0, 1)
        ax.set_ylim(-1, 1)

    def draw_1d_vstrip(rect, vec: np.ndarray):
        ax = add_box_ax(rect)
        disp, _ = signed_display(vec, gamma=0.78)
        ax.imshow(disp[:, None], aspect="auto", cmap=signed_cmap, vmin=-1.0, vmax=1.0, origin="lower", extent=[-1, 1, 0, 1])
        ax.axvline(0.0, color="#666666", lw=0.4, alpha=0.6)
        v_norm = vec / (np.max(np.abs(vec)) + 1e-15)
        ax.plot(0.78 * v_norm, np.linspace(0, 1, len(vec)), color="#111111", lw=0.9)
        ax.set_xlim(-1, 1)
        ax.set_ylim(0, 1)

    def draw_2d_tile(rect, tile: np.ndarray, caption: str, peak_override: float | None = None, fontsize: float = 7.2):
        ax = add_box_ax(rect)
        disp, pk = signed_display(tile, peak=peak_override, gamma=0.78)
        ax.imshow(disp, origin="lower", cmap=signed_cmap, vmin=-1.0, vmax=1.0, interpolation="bilinear")
        pk_val = float(np.max(np.abs(tile)))
        lbl = f"{caption} ($\\pm${pk_val:.2g})" if caption else f"$\\pm${pk_val:.2g}"
        fig.text(rect[0] + 0.5 * rect[2], rect[1] - 0.004, lbl, ha="center", va="top", fontsize=fontsize, color="#222222")

    # Background canvas axis for lines/brackets/labels across the figure
    bg = fig.add_axes([0, 0, 1, 1], frameon=False)
    bg.set_xlim(0, 1)
    bg.set_ylim(0, 1)
    bg.set_xticks([])
    bg.set_yticks([])

    def draw_sum_bracket(x_left_edge: float, y_centers: list[float], x_out_left: float, y_out: float):
        bar_x = 0.5 * (x_left_edge + x_out_left)
        for yc in y_centers:
            bg.plot([x_left_edge + 0.004, bar_x], [yc, yc], color="#555e6d", lw=1.0)
        bg.plot([bar_x, bar_x], [min(y_centers), max(y_centers)], color="#555e6d", lw=1.0)
        bg.plot([bar_x, x_out_left - 0.004], [y_out, y_out], color="#555e6d", lw=1.0)
        bg.text(bar_x, max(y_centers) + 0.013, r"$\Sigma$", ha="center", va="bottom", fontsize=9.5, color="#333b48")

    # =========================================================================
    # TOP HALF (y in [0.48, 0.99]): (a) Components vs. (b) Rendering terms
    # =========================================================================
    bg.text(0.245, 0.986, "(a) Mathematical \"Components\" view ($K = u_1 + u_2$, circular per component)",
            ha="center", va="top", fontsize=9.8, fontweight="bold", color="#111111")
    bg.text(0.755, 0.986, "(b) Computational \"Rendering terms\" view ($K = t_1 + t_2 + t_3 + t_4$, smallest first)",
            ha="center", va="top", fontsize=9.8, fontweight="bold", color="#111111")
    bg.plot([0.50, 0.50], [0.482, 0.986], color="#d0d5dd", lw=0.9, ls="--")

    tile_w = 0.051
    tile_h = tile_w * aspect  # square in physical inches (~0.0821)
    strip_thick_w = 0.0135
    strip_thick_h = strip_thick_w * aspect
    row_ys = [0.838, 0.728, 0.618, 0.508]  # bottom y of each of the 4 rows

    # --- Panel (a): Components ---
    xa_h = 0.018
    xa_v = xa_h + tile_w + 0.018
    xa_t0 = xa_v + strip_thick_w + 0.020
    xa_u = xa_t0 + tile_w + 0.045
    xa_K = xa_u + tile_w + 0.045

    raw_tiles = []
    for i in range(4):
        y0 = row_ys[i]
        yc = y0 + 0.5 * tile_h
        draw_1d_hstrip([xa_h, yc - 0.5 * strip_thick_h, tile_w, strip_thick_h], H_raw[i])
        bg.text(xa_h + tile_w + 0.009, yc, r"$\times$", ha="center", va="center", fontsize=10.5, color="#333333")
        draw_1d_vstrip([xa_v, y0, strip_thick_w, tile_h], V_raw[i])
        bg.text(xa_v + strip_thick_w + 0.010, yc, "$=$", ha="center", va="center", fontsize=10.0, color="#333333")
        t_ij = np.outer(V_raw[i], H_raw[i])
        raw_tiles.append(t_ij)
        draw_2d_tile([xa_t0, y0, tile_w, tile_h], t_ij, "")

    u1_tile = raw_tiles[0] + raw_tiles[1]
    u2_tile = raw_tiles[2] + raw_tiles[3]
    K_tile = u1_tile + u2_tile

    yc_rows = [y + 0.5 * tile_h for y in row_ys]
    yu1 = 0.5 * (yc_rows[0] + yc_rows[1])
    yu2 = 0.5 * (yc_rows[2] + yc_rows[3])
    yK = 0.5 * (yu1 + yu2)

    draw_sum_bracket(xa_t0 + tile_w, [yc_rows[0], yc_rows[1]], xa_u, yu1)
    draw_sum_bracket(xa_t0 + tile_w, [yc_rows[2], yc_rows[3]], xa_u, yu2)
    draw_2d_tile([xa_u, yu1 - 0.5 * tile_h, tile_w, tile_h], u1_tile, "$u_1$")
    draw_2d_tile([xa_u, yu2 - 0.5 * tile_h, tile_w, tile_h], u2_tile, "$u_2$")

    draw_sum_bracket(xa_u + tile_w, [yu1, yu2], xa_K, yK)
    draw_2d_tile([xa_K, yK - 0.5 * tile_h, tile_w, tile_h], K_tile, "$K$")
    y_col_hdr = row_ys[0] + tile_h + 0.012
    bg.text(xa_h + 0.5 * tile_w, y_col_hdr, "1-D horiz. $h(x)$", ha="center", va="bottom", fontsize=7.5, color="#444444")
    bg.text(xa_v + 0.5 * strip_thick_w, y_col_hdr, "$v(y)$", ha="center", va="bottom", fontsize=7.5, color="#444444")
    bg.text(xa_t0 + 0.5 * tile_w, y_col_hdr, "2-D product", ha="center", va="bottom", fontsize=7.5, color="#444444")
    bg.text(xa_u + 0.5 * tile_w, yu1 + 0.5 * tile_h + 0.012, "Circular\ncomponents", ha="center", va="bottom", fontsize=7.5, color="#444444")

    # --- Panel (b): Rendering terms (orthogonalized rowSpan, smallest first) ---
    xb_h = 0.540
    xb_v = xb_h + tile_w + 0.018
    xb_t0 = xb_v + strip_thick_w + 0.020
    xb_K = xb_t0 + tile_w + 0.050

    orth_tiles = []
    for i in range(4):
        y0 = row_ys[i]
        yc = y0 + 0.5 * tile_h
        bg.text(xb_h - 0.006, yc, f"$n{{=}}{i+1}$", ha="right", va="center", fontsize=7.3, color="#1f4e78")
        draw_1d_hstrip([xb_h, yc - 0.5 * strip_thick_h, tile_w, strip_thick_h], H_orth[i])
        bg.text(xb_h + tile_w + 0.009, yc, r"$\times$", ha="center", va="center", fontsize=10.5, color="#333333")
        draw_1d_vstrip([xb_v, y0, strip_thick_w, tile_h], V_orth[i])
        bg.text(xb_v + strip_thick_w + 0.010, yc, "$=$", ha="center", va="center", fontsize=10.0, color="#333333")
        t_ij = np.outer(V_orth[i], H_orth[i])
        orth_tiles.append(t_ij)
        sgn_lbl = "$-$" if np.dot(H_orth[i], V_orth[i]) < 0 else "$+$"
        draw_2d_tile([xb_t0, y0, tile_w, tile_h], t_ij, f"$t_{i+1}$({sgn_lbl})")

    K_orth_tile = sum(orth_tiles)
    draw_sum_bracket(xb_t0 + tile_w, yc_rows, xb_K, yK)
    draw_2d_tile([xb_K, yK - 0.5 * tile_h, tile_w, tile_h], K_orth_tile, "$K$")

    # Legend note for signed color scale at right of Panel (b)
    note_box = FancyBboxPatch((0.880, 0.520), 0.106, 0.165, boxstyle="round,pad=0.008",
                              fc="#f8f9fb", ec="#cfd6e0", lw=0.8)
    bg.add_patch(note_box)
    bg.text(0.933, 0.672, "Signed values", ha="center", va="top", fontsize=8.0, fontweight="bold", color="#222222")
    bg.text(0.933, 0.642, "Blue: $> 0$\nWhite: $0$\nRed: $< 0$\n\nEach tile scaled\nto its own $\\pm$peak.\nNo intermediate\nblowup in (b)!",
            ha="center", va="top", fontsize=7.0, color="#333333")

    bg.text(xb_h + 0.5 * tile_w, y_col_hdr, "1-D $\\tilde{h}_n(x)$", ha="center", va="bottom", fontsize=7.5, color="#444444")
    bg.text(xb_v + 0.5 * strip_thick_w, y_col_hdr, "$\\pm\\tilde{h}_n$", ha="center", va="bottom", fontsize=7.5, color="#444444")
    bg.text(xb_t0 + 0.5 * tile_w, y_col_hdr, "Rendering term $t_n$", ha="center", va="bottom", fontsize=7.5, color="#444444")

    # Horizontal divider separating kernel decomposition (top) and image pipeline (bottom)
    bg.plot([0.015, 0.985], [0.472, 0.472], color="#c5ccd6", lw=1.0)

    # =========================================================================
    # BOTTOM HALF (y in [0.015, 0.462]): (c) Step-by-step image pipeline with intermediates
    # =========================================================================
    bg.text(
        0.50, 0.460,
        "(c) Streaming 2-pass image convolution ($R = 4$): horizontal pass $m \\leftarrow I *_x \\tilde{h}_n$ "
        "(reusing one intermediate buffer $m$) followed by $A \\leftarrow A + m *_y \\tilde{v}_n$",
        ha="center", va="top", fontsize=9.6, fontweight="bold", color="#111111",
    )

    # Build a crisp 144x144 zero-background test patch with 2 bright point stars + a tilted geometric bar
    N_img = 144
    R_blur = 18.0
    L_tap = int(math.ceil(R_blur * S))
    x_tap = np.arange(-L_tap, L_tap + 1, dtype=np.float64) / R_blur
    H_t_raw, V_t_raw = per_component_channels_1d(x_tap, comps, S=S)
    H_t, V_t = orthogonal_rowspan_channels_1d(H_t_raw, V_t_raw)
    ksum = float(np.sum((H_t @ np.ones(H_t.shape[1])) * (V_t @ np.ones(V_t.shape[1]))))
    H_t = H_t / math.sqrt(abs(ksum))
    V_t = V_t / math.sqrt(abs(ksum)) * (1.0 if ksum > 0 else -1.0)

    # Scene-linear HDR test patch: dark night ambient (0.004 linear ~= 13/255 sRGB),
    # 2 bright 3x3 HDR point stars (48.0 & 24.0 linear -> blurred R=18 discs of ~0.43 & ~0.22 linear),
    # and a diffuse tilted bar (0.72 linear ~= 220/255 sRGB).
    img = np.full((N_img, N_img), 0.004, dtype=np.float64)
    yy, xx = np.meshgrid(np.arange(N_img), np.arange(N_img), indexing="ij")
    img[98:101, 38:41] = 48.0
    img[106:109, 98:101] = 24.0
    rot_u = (xx - 72) * math.cos(0.38) + (yy - 40) * math.sin(0.38)
    rot_v = -(xx - 72) * math.sin(0.38) + (yy - 40) * math.cos(0.38)
    bar_mask = (np.abs(rot_u) <= 34.0) & (np.abs(rot_v) <= 5.5)
    img[bar_mask] = 0.72

    m_steps = []
    dA_steps = []
    A_steps = []
    acc = np.zeros_like(img)
    for n in range(4):
        m_n = convolve1d(img, H_t[n], axis=1, mode="nearest")
        dA_n = convolve1d(m_n, V_t[n], axis=0, mode="nearest")
        acc = acc + dA_n
        m_steps.append(m_n)
        dA_steps.append(dA_n)
        A_steps.append(acc.copy())

    def linear_to_srgb_display(arr: np.ndarray) -> np.ndarray:
        """Exact IEC 61966-2-1 sRGB transfer function at fixed 1.0x linear exposure (no pedestal)."""
        c = np.clip(arr, 0.0, 1.0)
        return np.where(c <= 0.0031308, 12.92 * c, 1.055 * np.power(np.maximum(c, 1e-12), 1.0 / 2.4) - 0.055)

    b_tile_w = 0.066
    b_tile_h = b_tile_w * aspect  # ~0.1062
    y_b_rows = [0.288, 0.153, 0.018]  # m_n, dA_n, A_n

    # Left column: Sharp Input I (same unit linear exposure + exact sRGB as A_4!)
    x_in = 0.022
    ax_in = add_box_ax([x_in, 0.242, 0.094, 0.094 * aspect])
    ax_in.imshow(linear_to_srgb_display(img), origin="lower", cmap="gray", vmin=0.0, vmax=1.0, interpolation="nearest")
    bg.text(x_in + 0.047, 0.400, "Sharp HDR input $I$ (sRGB)", ha="center", va="bottom", fontsize=8.1, fontweight="bold", color="#111111")
    bg.text(x_in + 0.047, 0.232, "2 HDR stars ($48, 24$)\n+ diffuse bar ($0.72$)", ha="center", va="top", fontsize=7.0, color="#444444")

    loop_box = FancyBboxPatch((0.014, 0.020), 0.116, 0.168, boxstyle="round,pad=0.006",
                              fc="#f3f6fa", ec="#b8c4d4", lw=0.8)
    bg.add_patch(loop_box)
    bg.text(0.072, 0.180, "Streaming GPU loop", ha="center", va="top", fontsize=7.7, fontweight="bold", color="#163b66")
    bg.text(0.072, 0.152,
            "$A \\leftarrow 0$\nfor $n = 1 \\dots R$:\n  $m \\leftarrow I *_x \\tilde{h}_n$\n  $A \\leftarrow A + m *_y \\tilde{v}_n$\n\nOnly 1 temp image $m$\nin memory at once!",
            ha="center", va="top", fontsize=6.9, color="#222222")

    # Row labels on left of the 4 step columns
    x_lbl = 0.232
    bg.text(x_lbl, y_b_rows[0] + 0.5 * b_tile_h, "1. Horiz. pass\n$m \\leftarrow I *_x \\tilde{h}_n$\n(overwrites $m$)",
            ha="right", va="center", fontsize=7.4, color="#1f4e78", fontweight="bold")
    bg.text(x_lbl, y_b_rows[1] + 0.5 * b_tile_h, "2. Vert. pass\n$\\Delta A_n = m *_y \\tilde{v}_n$\n(2-D term patch)",
            ha="right", va="center", fontsize=7.4, color="#333333")
    bg.text(x_lbl, y_b_rows[2] + 0.5 * b_tile_h, "3. Accumulator\n$A_n = \\sum_{k=1}^n \\Delta A_k$\n(running sum)",
            ha="right", va="center", fontsize=7.4, color="#1c5e20", fontweight="bold")

    col_xs = [0.248 + n * 0.148 for n in range(4)]
    step_titles = [
        "Step $n=1$ ($t_1$, finest)",
        "Step $n=2$ ($t_2$, ripple)",
        "Step $n=3$ ($t_3$, ring)",
        "Step $n=4$ ($t_4$, core)",
    ]

    for n in range(4):
        xc = col_xs[n]
        bg.text(xc + 0.5 * b_tile_w, y_b_rows[0] + b_tile_h + 0.010, step_titles[n],
                ha="center", va="bottom", fontsize=7.9, fontweight="bold", color="#222222")

        # Row 0: 1-D horizontal intermediate m_n
        ax_m = add_box_ax([xc, y_b_rows[0], b_tile_w, b_tile_h])
        dm, pkm = signed_display(m_steps[n], gamma=0.72)
        ax_m.imshow(dm, origin="lower", cmap=signed_cmap, vmin=-1.0, vmax=1.0, interpolation="bilinear")
        bg.text(xc + b_tile_w + 0.004, y_b_rows[0] + 0.5 * b_tile_h, f"$\\pm${pkm:.2g}",
                ha="left", va="center", fontsize=6.9, color="#444444")

        # Downward arrow m_n -> dA_n
        bg.annotate("", xy=(xc + 0.5 * b_tile_w, y_b_rows[1] + b_tile_h + 0.003),
                    xytext=(xc + 0.5 * b_tile_w, y_b_rows[0] - 0.003),
                    arrowprops={"arrowstyle": "->", "lw": 0.85, "color": "#555e6d"})

        # Row 1: 2-D vertical pass output dA_n
        ax_da = add_box_ax([xc, y_b_rows[1], b_tile_w, b_tile_h])
        dda, pkda = signed_display(dA_steps[n], gamma=0.72)
        ax_da.imshow(dda, origin="lower", cmap=signed_cmap, vmin=-1.0, vmax=1.0, interpolation="bilinear")
        bg.text(xc + b_tile_w + 0.004, y_b_rows[1] + 0.5 * b_tile_h, f"$\\pm${pkda:.2g}",
                ha="left", va="center", fontsize=6.9, color="#444444")

        # Downward arrow dA_n -> A_n
        bg.annotate("", xy=(xc + 0.5 * b_tile_w, y_b_rows[2] + b_tile_h + 0.003),
                    xytext=(xc + 0.5 * b_tile_w, y_b_rows[1] - 0.003),
                    arrowprops={"arrowstyle": "->", "lw": 0.85, "color": "#2ca02c"})

        # Row 2: Running sum A_n
        ax_a = add_box_ax([xc, y_b_rows[2], b_tile_w, b_tile_h])
        da_acc, pka = signed_display(A_steps[n], gamma=0.72)
        ax_a.imshow(da_acc, origin="lower", cmap=signed_cmap, vmin=-1.0, vmax=1.0, interpolation="bilinear")
        bg.text(xc + b_tile_w + 0.004, y_b_rows[2] + 0.5 * b_tile_h, f"$\\pm${pka:.2g}",
                ha="left", va="center", fontsize=6.9, color="#444444")

        # Horizontal '+' arrow along the accumulator row A_1 -> A_2 -> A_3 -> A_4
        if n < 3:
            x_arrow_l = xc + b_tile_w + 0.036
            x_arrow_r = col_xs[n + 1] - 0.004
            ya_mid = y_b_rows[2] + 0.5 * b_tile_h
            bg.annotate("", xy=(x_arrow_r, ya_mid), xytext=(x_arrow_l, ya_mid),
                        arrowprops={"arrowstyle": "->", "lw": 1.0, "color": "#1c5e20"})
            bg.text(0.5 * (x_arrow_l + x_arrow_r), ya_mid + 0.008, "$+$", ha="center", va="bottom",
                    fontsize=8.5, fontweight="bold", color="#1c5e20")

    # Rightmost column: Final rendered bokeh photograph (exact sRGB at identical 1.0x exposure!)
    x_out = 0.858
    ax_out = add_box_ax([x_out, 0.218, 0.106, 0.106 * aspect])
    ax_out.imshow(linear_to_srgb_display(A_steps[-1]), origin="lower", cmap="gray", vmin=0.0, vmax=1.0, interpolation="bilinear")
    bg.text(x_out + 0.053, 0.396, "Rendered bokeh $A_4$ (sRGB)", ha="center", va="bottom", fontsize=8.1, fontweight="bold", color="#111111")
    bg.text(x_out + 0.053, 0.207, "Same $1\\times$ exposure, sRGB;\nstreaks cancel ($R{=}4$ $\\pm 7.6\\%$\nrings visible on $48\\times$ star)",
            ha="center", va="top", fontsize=6.7, color="#222222")

    # Arrow from A_4 to Rendered bokeh output
    bg.annotate("", xy=(x_out + 0.053, 0.145), xytext=(col_xs[3] + b_tile_w + 0.038, y_b_rows[2] + 0.5 * b_tile_h),
                arrowprops={"arrowstyle": "->", "lw": 1.1, "color": "#1c5e20", "connectionstyle": "arc3,rad=0.18"})

    pdf_path = os.path.join(paper_dir, "fig_overview_pipeline.pdf")
    fig.savefig(pdf_path)
    if preview_dir:
        fig.savefig(os.path.join(preview_dir, "fig_overview_pipeline.png"), dpi=200)
    plt.close(fig)
    print(f"Wrote {pdf_path}")


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
        ("1r_4 (deg 3 real)", "#8c564b", "-.", 1.2, r"Real poly $1r_4$ ($R{=}4$)"),
        ("1c (Gaussian)", "#ff7f0e", "-", 1.2, r"Complex $1c$ ($R{=}2$)"),
        ("1c+1r", "#2ca02c", "-", 1.25, r"Mixed $1c{+}1r$ ($R{=}3$)"),
        ("2c (Gaussian)", "#1f77b4", "-", 1.4, r"Complex $2c$ ($R{=}4$)"),
        ("6c (Gaussian)", "#d62728", "-", 1.5, r"Complex $6c$ ($R{=}12$)"),
    ]
    for key, col, ls, lw, lbl in curve_styles:
        ax.plot(r, data["profile_curves"][key], color=col, ls=ls, lw=lw, label=lbl)

    ax.set_xlim(0.0, 1.80)
    ax.set_ylim(-0.28, 1.26)
    ax.set_xlabel(r"Normalized radius $r = \sqrt{x^2 + y^2}$")
    ax.set_ylabel(r"Radial profile $\varphi(r^2)$")
    ax.set_title("(a) 2-D circular disc-blur profiles ($\\Delta r = 0.2$)")
    ax.grid(True, alpha=0.25, lw=0.5)
    ax.legend(loc="lower left", frameon=True, framealpha=0.93, fontsize=7.3)

    # --- Panel (b): Minimax ripple vs exact 2-D separable rank R ---
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
    ax.semilogy(x_cg, y_cg, "o-", color="#1f77b4", lw=1.6, ms=5.6, label=r"Distinct complex Gaussians ($n_{\mathrm{cx}}{=}1\dots 6$)")
    ax.semilogy(x_mg, y_mg, "D", color="#2ca02c", ms=5.8, label=r"Odd-rank mixed ($n_{\mathrm{cx}}$ complex + $1$ real)")

    # Also plot 1c+1r_2 at R=4
    mp = [f for f in fams if f["kind_group"] == "mixed_poly"][0]
    ax.semilogy([mp["rank_2d"]], [mp["ripple_2d"]], "P", color="#17becf", ms=6.8, label=r"Mixed $1c + 1r_2$ ($R{=}4, C_3{=}6$)")

    ax.annotate(
        r"$R{=}4$: $2c$ ($C_3{=}6$)" "\n" r"beats $1c_2$ ($C_3{=}7$)",
        xy=(4, 0.07593), xytext=(5.5, 0.16),
        arrowprops={"arrowstyle": "->", "lw": 0.8, "color": "#333333"},
        fontsize=7.6, bbox={"boxstyle": "round,pad=0.2", "fc": "#f8f9fa", "ec": "#cccccc", "lw": 0.6},
    )

    ax.set_xticks(range(2, 13))
    ax.set_ylim(1.2e-3, 0.5)
    ax.set_xlabel(r"Exact 2-way real separable rank $R$")
    ax.set_ylabel(r"Chebyshev pass/stopband ripple $\max |\varphi - \mathbf{1}_{r \leq 1}|$")
    ax.set_title("(b) Chebyshev ripple vs. exact rank $R$")
    ax.grid(True, which="both", alpha=0.25, lw=0.5)
    ax.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.3)

    # --- Panel (c): Conditioning & float16 bokeh error ---
    ax = axes[2]
    cond = data["conditioning"]
    cg_cond = sorted([c for c in cond if c["kind_group"] == "complex_gaussian"], key=lambda c: c["rank_2d"])
    cp_cond = sorted([c for c in cond if c["kind_group"] == "complex_poly"], key=lambda c: c["rank_2d"])

    ax.semilogy(
        [c["rank_2d"] for c in cg_cond], [c["fp16_max_raw_255"] for c in cg_cond],
        "o--", color="#d62728", lw=1.4, ms=5.2, label=r"Per-comp. ($n_{\mathrm{cx}}$ Gaussians)",
    )
    ax.semilogy(
        [c["rank_2d"] for c in cp_cond], [c["fp16_max_raw_255"] for c in cp_cond],
        "^--", color="#ff7f0e", lw=1.3, ms=5.2, label=r"Per-comp. ($1c_m$ poly)",
    )
    ax.semilogy(
        [c["rank_2d"] for c in cg_cond], [c["fp16_max_orth_255"] for c in cg_cond],
        "o-", color="#1f77b4", lw=1.6, ms=5.4, label=r"Orthog. $\mathrm{rowSpan}$ ($n_{\mathrm{cx}}$ Gauss.)",
    )
    ax.semilogy(
        [c["rank_2d"] for c in cp_cond], [c["fp16_max_orth_255"] for c in cp_cond],
        "^-", color="#2ca02c", lw=1.3, ms=5.0, label=r"Orthog. $\mathrm{rowSpan}$ ($1c_m$ poly)",
    )
    ax.axhline(1.0, color="#444444", ls=":", lw=1.0, label="1.0 / 255 (8-bit LSB)")

    ax.annotate(
        f"Amp $1110\\times \\to 2.32\\times$\n(${cp_cond[-1]['fp16_max_raw_255']:.2f} \\to {cp_cond[-1]['fp16_max_orth_255']:.2f} / 255$)",
        xy=(12, cp_cond[-1]["fp16_max_raw_255"]), xytext=(7.2, 0.48),
        arrowprops={"arrowstyle": "->", "lw": 0.8, "color": "#444444"},
        fontsize=7.0, bbox={"boxstyle": "round,pad=0.2", "fc": "#fff8f6", "ec": "#ddbbaa", "lw": 0.6},
    )

    ax.set_xticks([2, 4, 6, 8, 10, 12])
    ax.set_ylim(0.06, 26.0)
    ax.set_xlabel(r"Exact 2-way real separable rank $R$")
    ax.set_ylabel("Max float16 bokeh error (8-bit sRGB / 255)")
    ax.set_title(r"(c) $\mathrm{GL}_R(\mathbb{R})$ rebalancing & float16 sRGB error")
    ax.grid(True, which="both", alpha=0.25, lw=0.5)
    ax.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=6.7)

    pdf_path = os.path.join(paper_dir, "fig_blur_2d.pdf")
    fig.savefig(pdf_path)
    if preview_dir:
        fig.savefig(os.path.join(preview_dir, "fig_blur_2d.png"), dpi=200)
    plt.close(fig)
    print(f"Wrote {pdf_path}")


def make_discrete_vs_continuous_figure(app_dir: str, paper_dir: str, preview_dir: str | None = None):
    """
    Visual and quantitative comparison at exact rank R = 4 between:
      (1) Sampled continuous complex-Gaussian 2c,
      (2) Direct SVD (Eckart-Young l_2-optimal rank-4 truncation of smooth raised-cosine disc),
      (3) Unconstrained discrete rank-4 minimax (pass/stopband Chebyshev), and
      (4) Shell-isotropic discrete rank-4 minimax (equal-Euclidean-radius shells constrained equal),
    across small (R_px = 6, W = 17) and large (R_px = 25, W = 61) stencils.
    """
    with open(os.path.join(app_dir, "results_blur_2d.json"), "r", encoding="utf-8") as f:
        data = json.load(f)

    dvc = data["discrete_vs_continuous"]
    summary = {(r["radius_px"], r["rank_R"]): r for r in dvc["summary"]}
    ker6 = {k: np.array(v, dtype=np.float64) for k, v in dvc["kernels_R4"]["Rpx6_R4"].items()}
    ker25 = {k: np.array(v, dtype=np.float64) for k, v in dvc["kernels_R4"]["Rpx25_R4"].items()}

    def srgb_encode(arr: np.ndarray) -> np.ndarray:
        c = np.clip(arr, 0.0, 1.0)
        return np.where(c <= 0.0031308, 12.92 * c, 1.055 * np.power(np.maximum(c, 1e-12), 1.0 / 2.4) - 0.055)

    def render_two_star_bokeh(K: np.ndarray, R_px: int) -> np.ndarray:
        """
        Render two point stars on a dark night-sky background (0.004 linear ~= 13/255 sRGB)
        convolved with normalized K (sum K = 1) and encoded with exact IEC 61966-2-1 sRGB at 1x exposure:
          - Left star: moderate flux so blurred bokeh disc has peak ~0.52 linear (~0.75 sRGB, unclipped rim & interior!)
          - Right star: 12x brighter HDR star (~6.2 linear disc peak) so stopband halo / streaks are clearly visible!
        """
        Kn = K / np.sum(K)
        L = Kn.shape[0] // 2
        # Patch size: height = 3.2 * R_px, width = 6.2 * R_px
        H_p = int(round(3.5 * R_px))
        if H_p % 2 == 0:
            H_p += 1
        W_p = int(round(6.6 * R_px))
        if W_p % 2 == 0:
            W_p += 1
        out = np.full((H_p, W_p), 0.004, dtype=np.float64)
        cy = H_p // 2
        cx_l = int(round(1.75 * R_px))
        cx_r = W_p - 1 - cx_l

        # Stamp normalized kernel centered at (cy, cx_l) and (cy, cx_r)
        disc_area = math.pi * (R_px**2)
        flux_mod = 0.52 * disc_area
        flux_hdr = 6.20 * disc_area
        for cx_s, flux in [(cx_l, flux_mod), (cx_r, flux_hdr)]:
            y0, y1 = max(0, cy - L), min(H_p, cy + L + 1)
            x0, x1 = max(0, cx_s - L), min(W_p, cx_s + L + 1)
            ky0, ky1 = y0 - (cy - L), y1 - (cy - L)
            kx0, kx1 = x0 - (cx_s - L), x1 - (cx_s - L)
            out[y0:y1, x0:x1] += flux * Kn[ky0:ky1, kx0:kx1]
        return srgb_encode(out)

    cols = [
        ("cont", "Sampled continuous $2c$"),
        ("svd", "Direct SVD ($\\ell_2$ raised-cos)"),
        ("disc_uncon", "Discrete minimax (unconstr.)"),
        ("disc_iso", "Discrete minimax (shell-iso.)"),
    ]

    fig = plt.figure(figsize=(12.2, 7.6))
    gs = fig.add_gridspec(3, 4, height_ratios=[1.0, 1.0, 1.28], hspace=0.44, wspace=0.20,
                          left=0.055, right=0.988, top=0.935, bottom=0.075)

    for c_idx, (key, title) in enumerate(cols):
        m6 = summary[(6, 4)][key]
        m25 = summary[(25, 4)][key]

        # Row 0: Small stencil R_px = 6 (W = 17) rendered sRGB bokeh (moderate + 12x HDR star)
        ax0 = fig.add_subplot(gs[0, c_idx])
        im6 = render_two_star_bokeh(ker6[key], 6)
        ax0.imshow(im6, origin="lower", cmap="gray", vmin=0.0, vmax=1.0, interpolation="nearest")
        ax0.set_xticks([])
        ax0.set_yticks([])
        ax0.set_title(
            f"{title}\n"
            f"$R_{{\\mathrm{{px}}}}={{6}}$: rip ${m6['ripple']:.4f}$, aniso ${m6['shell_aniso']:.3f}$",
            fontsize=8.3, pad=4,
        )
        if c_idx == 0:
            ax0.set_ylabel("Small ($R_{\\mathrm{px}}{=}6, W{=}17$)\n1x + 12x stars (sRGB)", fontsize=8.0)

        # Row 1: Large stencil R_px = 25 (W = 61) rendered sRGB bokeh (moderate + 12x HDR star)
        ax1 = fig.add_subplot(gs[1, c_idx])
        im25 = render_two_star_bokeh(ker25[key], 25)
        ax1.imshow(im25, origin="lower", cmap="gray", vmin=0.0, vmax=1.0, interpolation="bilinear")
        ax1.set_xticks([])
        ax1.set_yticks([])
        ax1.set_title(
            f"$R_{{\\mathrm{{px}}}}={{25}}$: rip ${m25['ripple']:.4f}$, aniso ${m25['shell_aniso']:.3f}$",
            fontsize=8.2, pad=3,
        )
        if c_idx == 0:
            ax1.set_ylabel("Large ($R_{\\mathrm{px}}{=}25, W{=}61$)\n1x + 12x stars (sRGB)", fontsize=8.0)

        # Row 2: Per-pixel radial scatter K[mx,my] vs r/R_px at R_px = 6 (open circles) & R_px = 25 (dots),
        # colored by lattice angle theta in [0, 45 deg] (blue = 0 deg axis, red = 45 deg diagonal),
        # plus upper-right inset showing the R_px = 6 half-max contour K = 0.5 vs circle!
        ax2 = fig.add_subplot(gs[2, c_idx])
        ax2.axvspan(1.0, 1.2, color="#dfe6ef", alpha=0.55, lw=0)
        ax2.axhline(1.0, color="#666666", ls="--", lw=0.7)
        ax2.axhline(0.0, color="#666666", ls="--", lw=0.7)

        # Plot R_px = 25 pixels colored by angle in [0, pi/4]
        K25 = ker25[key]
        L25 = K25.shape[0] // 2
        m_arr25 = np.arange(-L25, L25 + 1, dtype=np.float64)
        mx25, my25 = np.meshgrid(m_arr25, m_arr25, indexing="ij")
        mask_oct25 = (mx25 >= 0) & (my25 >= 0) & (my25 <= mx25)
        r25_pts = np.sqrt(mx25[mask_oct25] ** 2 + my25[mask_oct25] ** 2) / 25.0
        th25_pts = np.arctan2(my25[mask_oct25], np.maximum(mx25[mask_oct25], 1e-12)) / (0.25 * math.pi)
        v25_pts = K25[mask_oct25]
        ax2.scatter(r25_pts, v25_pts, c=th25_pts, cmap="coolwarm", vmin=0.0, vmax=1.0,
                    s=7.0, alpha=0.82, edgecolors="none", zorder=3)

        # Overlay R_px = 6 axis (0 deg) vs diagonal (45 deg) markers so small-grid spread is crystal clear
        K6 = ker6[key]
        L6 = K6.shape[0] // 2
        m6_pos = np.arange(0, L6 + 1, dtype=np.float64)
        ax2.plot(m6_pos / 6.0, K6[L6 + m6_pos.astype(int), L6], "o", ms=3.6, mfc="none", mec="#0b4f8a", mew=0.9,
                 label=r"$R_{\mathrm{px}}{=}6$ ($0^\circ$)" if c_idx == 0 else None, zorder=4)
        ax2.plot(m6_pos * math.sqrt(2.0) / 6.0, K6[L6 + m6_pos.astype(int), L6 + m6_pos.astype(int)], "^",
                 ms=3.8, mfc="none", mec="#b2182b", mew=0.9,
                 label=r"$R_{\mathrm{px}}{=}6$ ($45^\circ$)" if c_idx == 0 else None, zorder=4)

        ax2.set_xlim(0.0, 1.72)
        ax2.set_ylim(-0.24, 1.24)
        ax2.set_xlabel(r"Normalized radius $r = \|\mathbf{m}\|_2 / R_{\mathrm{px}}$", fontsize=8.0)
        if c_idx == 0:
            ax2.set_ylabel(r"Stencil value $K[\mathbf{m}]$", fontsize=8.2)
            ax2.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=6.6)
        else:
            ax2.set_yticklabels([])
        ax2.grid(True, alpha=0.25, lw=0.5)

        # Small inset in upper-right of ax2: K = 0.5 rim contour at R_px = 6 (solid red) & R_px = 25 (solid blue) vs circle!
        ins = ax2.inset_axes([0.62, 0.54, 0.35, 0.42])
        th_c = np.linspace(0.0, 2.0 * math.pi, 200)
        ins.plot(1.09 * np.cos(th_c), 1.09 * np.sin(th_c), "k:", lw=0.75)
        g6 = np.arange(-L6, L6 + 1, dtype=np.float64) / 6.0
        ins.contour(g6, g6, K6, levels=[0.5], colors=["#d62728"], linewidths=1.0)
        g25 = np.arange(-L25, L25 + 1, dtype=np.float64) / 25.0
        ins.contour(g25, g25, K25, levels=[0.5], colors=["#1f77b4"], linewidths=0.9, linestyles="--")
        ins.set_xlim(-1.35, 1.35)
        ins.set_ylim(-1.35, 1.35)
        ins.set_aspect("equal")
        ins.set_xticks([])
        ins.set_yticks([])
        ins.set_title("$K{=}0.5$ rim", fontsize=6.4, pad=1.5)

    pdf_path = os.path.join(paper_dir, "fig_discrete_vs_continuous.pdf")
    fig.savefig(pdf_path)
    if preview_dir:
        fig.savefig(os.path.join(preview_dir, "fig_discrete_vs_continuous.png"), dpi=220)
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
        ("27-pt IWB (nu=1.00)", "#ff7f0e", r"27-pt IWB ($\nu{=}1, R{=}1$ Gauss.)"),
        ("25-pt O(dx^4,dt^4) FDTD (nu=1/sqrt3)", "#8c564b", r"25-pt $O(\Delta x^4,\Delta t^4)$ ($\nu{=}1/\sqrt{3}$)"),
        ("Rank-7 (2c+1r, nu=1.00)", "#1f77b4", r"Rank-7 ($2c{+}1r, \nu{=}1, W{=}13$)"),
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

    # Inset zoom placed cleanly above the 4-row legend!
    ax_in = ax_disp.inset_axes([0.07, 0.355, 0.45, 0.415])
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
    ax_wf.plot(s_7pt["ct"], s_7pt["traces"]["face_diag"], color="#d62728", lw=1.1, alpha=0.9,
               label=rf"7-pt FDTD (rel $L^2 = {100*s_7pt['rel_l2']['face_diag']:.1f}\%$)")
    ax_wf.plot(s_iwb["ct"], s_iwb["traces"]["face_diag"], color="#ff7f0e", lw=1.15, ls="--", alpha=0.95,
               label=rf"27-pt IWB $\nu{{=}}1$ (rel $L^2 = {100*s_iwb['rel_l2']['face_diag']:.1f}\%$)")
    ax_wf.plot(s_r7_075["ct"], s_r7_075["traces"]["face_diag"], "o-", color="#2ca02c", lw=1.0, ms=2.6, alpha=0.9,
               label=rf"Rank-7 $2c{{+}}1r, \nu{{=}}0.75$ (rel $L^2 = {100*s_r7_075['rel_l2']['face_diag']:.1f}\%$)")
    ax_wf.plot(ct_ref, s_ref["traces"]["face_diag"], "s:", color="#1f77b4", lw=1.1, ms=3.0,
               label=rf"Rank-7 $2c{{+}}1r, \nu{{=}}1.00$ (rel $L^2 = {100*s_ref['rel_l2']['face_diag']:.1f}\%$)")

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
    import sys
    configure_style()
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    app_dir = os.path.join(repo_root, "Applications")
    paper_dir = os.path.join(repo_root, "paper")
    preview_dir = os.path.join(repo_root, ".tmp") if "--preview" in sys.argv else None
    make_overview_pipeline_figure(app_dir, paper_dir, preview_dir=preview_dir)
    make_blur_2d_figure(app_dir, paper_dir, preview_dir=preview_dir)
    make_discrete_vs_continuous_figure(app_dir, paper_dir, preview_dir=preview_dir)
    make_acoustics_3d_figure(app_dir, paper_dir, preview_dir=preview_dir)


if __name__ == "__main__":
    main()
