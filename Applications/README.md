# Numerical applications and GPU benchmarks

This directory accompanies Section 5 of [`../paper/main.tex`](../paper/main.tex). All scripts run
through [`../scripts/python`](../scripts/python), which manages an isolated virtual environment in
`.tmp/venv` and keeps Matplotlib, `uv`, and Triton caches inside `.tmp/cache`.

## Files

| File | Description |
|---|---|
| [`blur_2d.py`](./blur_2d.py) | Minimax 2-D circular disc blur ($\tau = 0.2$) across 18 exponential-polynomial families; empirical SVD rank checks; nuclear-norm-optimal $\mathrm{GL}_N(\mathbb{R})$ rebalancing on $\mathrm{rowSpan}(K)$ vs. IEEE `float16` HDR bokeh error; 1080p RGBA Triton GPU benchmarks |
| [`acoustics_3d.py`](./acoustics_3d.py) | Algebraic identity between Kowalczyk–van Walstijn's 27-point `IWB` stencil and a single real Gaussian ($R = 1$); $65^3$ Brillouin-octant (47,904-point) certified minimax LP design of von Neumann-stable 3-D radial wave propagators ($R = 4, 6, 7, 9$, including $\deg P = 1$); $256^3$ broadband spherical wave simulation vs. exact 3-D D'Alembert; 1,000-step rigid-room Neumann wall energy test; Triton GPU benchmarks |
| [`generate_figures.py`](./generate_figures.py) | Generates [`../paper/fig_blur_2d.pdf`](../paper/fig_blur_2d.pdf) and [`../paper/fig_acoustics_3d.pdf`](../paper/fig_acoustics_3d.pdf) from the JSON artifacts |
| [`results_blur_2d.json`](./results_blur_2d.json), [`results_acoustics_3d.json`](./results_acoustics_3d.json) | Saved optimization parameters, error metrics, waveforms, and NVIDIA GeForce RTX 4070 Ti Super benchmark timings |

## Reproducing everything

From the repository root (requires a CUDA-capable GPU for PyTorch/Triton benchmarks):

```sh
scripts/python Applications/blur_2d.py
scripts/python Applications/acoustics_3d.py
scripts/python Applications/generate_figures.py
scripts/build-paper
```
