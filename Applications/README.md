# Numerical applications and GPU benchmarks

This directory accompanies Section 5 and Appendix A of [`../paper/main.tex`](../paper/main.tex). All scripts run
through [`../scripts/python`](../scripts/python), which manages an isolated virtual environment in
`.tmp/venv` and keeps Matplotlib, `uv`, and Triton caches inside `.tmp/cache`.

## Files

| File | Description |
|---|---|
| [`blur_2d.py`](./blur_2d.py) | Minimax 2-D circular disc blur ($\Delta r = 0.2$) across 18 exponential-polynomial families; empirical SVD rank checks; 6-stage `separableChannels` IEEE `float16` conditioning ablation (comparing `GL_R` orthogonalization against magnitude reordering and `float32` outer accumulation without orthogonalization, `--ablation-only`) across 20 random HDR scenes and 3 glint peak levels; direct discrete rank-$R$ optimization vs. sampled continuous profiles, dense $R_{\mathrm{px}} \in [3, 64]$ convergence sweep, and warm-start vs. cold-start POCS trajectories (`--discrete-only`); 1080p RGBA 10-batch CUDA-Event GPU benchmarks against direct $W \times W$ convolution and zero- and clamp-padded `cuFFT`, each checked against a `float64` reference; 14-core CPU benchmarks |
| [`acoustics_3d.py`](./acoustics_3d.py) | Algebraic identity between Kowalczyk–van Walstijn's 27-point `IWB` stencil and a single real Gaussian ($R = 1$); Brillouin-octant and spherical-shell (232,620-point) Chebyshev LP design + continuous multi-start error refinement of von Neumann-stable 3-D radial wave propagators ($R = 4, 6, 7, 9$, including $\deg P = 1$); $256^3$ broadband spherical wave simulation vs. exact 3-D D'Alembert across 7-pt, 13-pt $O(\Delta x^4, \Delta t^2)$, 27-pt `IWB`, fourth-order 25-pt $O(\Delta x^4, \Delta t^4)$, and periodic `cuFFT` $k$-space propagation; shared-rate `Rank-8` spatially varying sound-speed $c(\mathbf{x})$ dispersion, 1,000-step smooth/jump stability, and $128^3$ acoustic focusing lens refraction (`--hetero-only`); 1,000-step rigid-room Neumann wall energy test; 10-batch GPU benchmarks of the separable, direct $W^3$ and $k$-space steps, each checked against a `float64` step; 14-core CPU benchmarks |
| [`gpu_kernels.py`](./gpu_kernels.py) | The GPU implementations used by both scripts (see [GPU implementations](#gpu-implementations)) |
| [`generate_figures.py`](./generate_figures.py) | Generates [`../paper/fig_overview_pipeline.pdf`](../paper/fig_overview_pipeline.pdf), [`../paper/fig_blur_2d.pdf`](../paper/fig_blur_2d.pdf), [`../paper/fig_discrete_vs_continuous.pdf`](../paper/fig_discrete_vs_continuous.pdf), [`../paper/fig_discrete_convergence.pdf`](../paper/fig_discrete_convergence.pdf), [`../paper/fig_acoustics_3d.pdf`](../paper/fig_acoustics_3d.pdf), and [`../paper/fig_acoustics_hetero.pdf`](../paper/fig_acoustics_hetero.pdf) from the JSON artifacts |
| [`results_blur_2d.json`](./results_blur_2d.json), [`results_acoustics_3d.json`](./results_acoustics_3d.json) | Saved optimization parameters, error metrics, waveforms, and NVIDIA GeForce RTX 4070 Ti Super benchmark timings with per-method errors and tuned launch parameters (`gpu_benchmark_info` describes the test data and methods) |
| [`requirements.txt`](./requirements.txt) | Python package list bootstrapped automatically into `.tmp/venv` by [`../scripts/python`](../scripts/python) (with reference versions noted) |

## Reproducing everything

From the repository root (requires a CUDA-capable GPU for PyTorch/Triton benchmarks; [`../scripts/python`](../scripts/python) and [`../scripts/build-paper`](../scripts/build-paper) automatically download static `uv` and `tectonic` binaries into `.tmp/bin` when needed):

```sh
scripts/python Applications/blur_2d.py
scripts/python Applications/acoustics_3d.py
scripts/python Applications/generate_figures.py
scripts/build-paper
```

Running these four commands recomputes the JSON archives on your hardware, regenerates all six vector PDF
figures from those JSON files, and recompiles [`../paper/main.pdf`](../paper/main.pdf) with the updated
figures (numerical tables and prose timings in [`../paper/main.tex`](../paper/main.tex) are static LaTeX text
recording our RTX 4070 Ti Super reference run).

`scripts/python Applications/blur_2d.py --gpu-only` (`--discrete-only`, `--ablation-only`) reruns only the GPU throughput
benchmark (or discrete-vs.-continuous convergence / warm-start analysis, or 6-stage `float16` conditioning ablation) from the stored kernel families,
and `scripts/python Applications/acoustics_3d.py --gpu-only` (`--hetero-only`) reruns only the GPU wave
simulation, room test and throughput benchmarks (or spatially varying $c(\mathbf{x})$ experiment) from the
stored propagators; all five flags update the JSON files in place. The first run compiles and tunes the Triton kernels (about half an hour for the 2-D benchmark); later
runs reuse `.tmp/cache/triton` and take a few minutes.

## GPU implementations

On the benchmark GPU, one pass over a $1920 \times 1080$ RGBA `float32` frame or a $256^3$ `float32` field
through DRAM costs about $0.05$–$0.1$ ms per buffer, while arithmetic and L2-cache traffic are several times
faster. All implementations in [`gpu_kernels.py`](./gpu_kernels.py) are organized around that, and every
benchmark row stores the maximum and root-mean-square error of each method against a `float64` reference
(`err_max_*`, `err_rms_*`), with assertions that fail the run on a regression.

- **Separable cascades** (`SeparableBlur2D`, `SeparableStep3D`). (1) *Register sliding windows:* a program
  computes $K$ consecutive outputs along the filtered axis and keeps the $K$ rows on each side of the
  symmetric FIR in registers, so a tap needs one new row load per side for all $K$ outputs. (2) *All terms
  per pass:* the first pass loads each input row once and updates all $R$ terms; the last pass sums all $R$
  terms. (3) *Cache-resident intermediates:* the frame is processed in strips of rows, and the volume in
  slabs of $x$-planes, sized so that the $R$ intermediate channels stay in the L2 cache; only the input and
  output cross DRAM. A window needs the filtered axis to be strided in memory, so the 2-D strips are stored
  transposed between the two passes, and the 3-D step filters the contiguous $z$ axis last with each thread
  owning a short run of $z$ values.
- **Direct convolution** (`DirectBlur2D`, `DirectStep3D`). Dense $W^2$ and $W^3$ Triton kernels in which each
  loaded row segment feeds several output rows or planes; the 3-D step reads a $z$-padded copy of the field so
  that no index reflection is needed in the inner loop.
- **`cuFFT`** (`FFTBlur2D`, `KSpaceStep3D`). The 2-D blur packs channel pairs into complex planes (the kernel
  is real, so one complex 2-D transform with in-place real spectral multiply filters two channels), centers the even kernel at the origin so
  its spectrum is real, folds the normalization into it, and picks the fastest $7$-smooth period of at least
  the image size plus $L$ (zero padding) or $2L$ (clamped borders). The 3-D $k$-space step splits the
  transform into L2-resident chunks: 2-D real transforms per group of $x$-planes, then the $x$ transform,
  spectral multiply and inverse $x$ transform per group of $y$-rows.
- **Tuning.** Window sizes, block shapes, strip or slab sizes and FFT periods are chosen by timing a few
  candidates at start-up; the chosen values are stored with each result (`config_*`).

Limitations: timings are for one GPU and one software stack, and the tuned parameters are specific to it.
Between two complete runs the mean timings differed by up to 6% (2-D) and 3% (3-D), more than the stored
within-run standard deviations, because the tuner can pick different parameters and buffers land at
different addresses.
The `float16` 2-D pipeline stores input, intermediates and output in `float16`; with intermediates no longer
crossing DRAM it is not consistently faster than `float32`. Half-precision `cuFFT` was not used because it
overflows on unnormalized transforms of this size. The single-pass FDTD kernels are unchanged: they already
run at the DRAM-bandwidth limit.
