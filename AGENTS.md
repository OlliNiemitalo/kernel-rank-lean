# Notes for agents working on kernel-rank-lean

## Repository layout

- `KernelRankLean/` and `KernelRankLean.lean`: the proof of the `d`-dimensional and 2-D
  separable-rank theorems for circularly symmetric kernels (`separableRank_radial_lt_top_iff_exists`,
  `separableRank_radial_eq_iff`, `separableRank_radial_two_eq_iff`,
  `separableRank_radial_complex_eq_iff`, `separableRank_radial_profile`, and
  `separableRank_radial_gaussian_profile` in `Main.lean` / `MultiRealRank.lean`). It must stay
  free of `sorry`; its axioms are only `propext`, `Classical.choice`, `Quot.sound`.
- `Experiments/` and `Experiments.lean`: alternative proofs of the semigroup step, none used
  by the main proof and all free of `sorry`: finite differences (`GeneratorBound.lean`,
  `FiniteDifferenceSemigroup.lean`), nonstandard analysis with sequences
  (`NonstandardSemigroup.lean`), and nonstandard analysis in nonstandard language
  (`Ultrapower.lean`, a general interface, and `UltrapowerSemigroup.lean`). Built by default
  (`lakefile.toml`). `Experiments/README.md` describes and compares them, with line counts;
  update it when any of them, or the Isabelle theory, changes.
- `Isabelle/`: an Isabelle/HOL version of the nonstandard semigroup proof (session
  `KernelRank_NSA`, theory `Semigroup_NSA.thy`), also described in `Experiments/README.md`.
  All nonstandard proofs share the same normalization (see "Mathematics of the nonstandard
  proofs" below).
- `Applications/`: reproducible Python/SciPy/PyTorch/Triton numerical optimization, simulation,
  and GPU benchmark scripts (`blur_2d.py`, `acoustics_3d.py`, `generate_figures.py`, JSON
  results) accompanying Section 5 of the paper; run via `scripts/python` (which keeps `.tmp/venv`
  and all Matplotlib/`uv`/Triton caches inside `.tmp/`). `gpu_kernels.py` holds the GPU
  implementations (separable, direct, `cuFFT`) used by both scripts; see "GPU benchmarks" below.
  `--gpu-only` on either script reruns only its GPU parts from the stored optimization results;
  `--discrete-only` on `blur_2d.py` reruns only discrete-vs.-continuous convergence and warm-start
  analyses; `--hetero-only` on `acoustics_3d.py` reruns only the spatially varying $c(\mathbf{x})$
  experiment.
- `paper/`: LaTeX source (`main.tex`), vector figures (`fig_overview_pipeline.pdf`,
  `fig_blur_2d.pdf`, `fig_discrete_vs_continuous.pdf`, `fig_discrete_convergence.pdf`,
  `fig_acoustics_3d.pdf`, `fig_acoustics_hetero.pdf`), compiled PDF (`main.pdf`), and metadata (`metadata.json`) for the
  aiXiv preprint `aixiv.261111.000007`; built via `scripts/build-paper` (static Tectonic in
  `.tmp/bin`) and submitted/updated via `scripts/submit-aixiv` (reads
  `AIXIV_GITHUB_COPILOT_TOKEN` from the environment; never commit tokens).
- `scripts/`: tool wrappers, setup, paper scripts, and the check script; `.githooks/`: the
  pre-commit hook.
- `README.md`: theorem statements, potential applications, file table, commit history with Lean
  line counts, a summary of the alternative proofs, and the suggested kernel-optimizer citation.

## Toolchain and commands

- **Work with files, not long command lines.** Edit sources with the edit tool; put any
  multi-step or reusable shell logic in a script file (under `scripts/` if useful to others,
  else `.tmp/`) and run it with a short command. No long heredocs or inline Python in commands.
- `scripts/isabelle-report DIR SESSION` builds a development session (for example a copy of
  a theory in `.tmp/sh`) and prints errors, commands over 20 s, and Sledgehammer suggestions;
  full output in `.tmp/reports/`. It is for development only; `scripts/check` is the
  verification. Never use `quick_and_dirty` (the script refuses it): to ask Sledgehammer,
  state each open goal as a standalone lemma ending in `oops` in a separate scratch session.
  Sledgehammer only runs if no earlier command hangs, so set a session `timeout` and fix
  slow commands first.
- **Stay inside the repository.** Work from the repository root and never `cd` (not even into
  `.tmp/` and back); use repository-relative paths instead. All tools, caches, build
  outputs and scratch files live under the ignored `.tmp/` directory, never elsewhere (such as
  `/tmp` or `~`), so commands need no extra approval. `scripts/env.sh` sets this up:
  `ELAN_HOME=.tmp/elan`, `XDG_CACHE_HOME` and `MATHLIB_CACHE_DIR` under `.tmp/cache`.
  Always use the wrappers `scripts/lake` and `scripts/isabelle`, never bare `lake` or
  `isabelle`.
- `scripts/setup` (once): installs elan and Isabelle2026 into `.tmp/` and sets
  `git config core.hooksPath .githooks`.
- **Checks.** `scripts/check [--force] [lean] [isabelle]` is the single check used both during
  work and by the pre-commit hook (`.githooks/pre-commit`, which adds `git diff --cached
  --check` and `--staged`); there is no GitHub CI for the proofs. A passing component writes
  `.tmp/checks/<component>.stamp`, keyed by a hash of the git blob ids of its inputs (sources,
  build files, toolchain version, the scripts) as in the working tree. The hook requires the
  inputs to have no unstaged or untracked changes and reruns only components whose key
  changed. Run `scripts/check` after finishing work, so the commit is instant. Logs are in
  `.tmp/checks/<component>.log`.
  - `lean`: `lake exe cache get`, `lake build` (both libraries), no `sorry` in any Lean
    file, and `#print axioms` on the main theorems and the alternative proofs
    (`.tmp/checks/Axioms.lean`) must give only `propext`, `Classical.choice`, `Quot.sound`.
    Add new key theorems to `lean_theorems` in `scripts/check`.
  - `isabelle`: builds `KernelRank_NSA`, then a generated session
    (`.tmp/checks/isabelle-audit`) checks with `Thm_Deps.all_oracles` that the theorems in
    `isabelle_theorems` use no oracle. This catches `sorry` (the `skip_proof` oracle) even if
    `Isabelle/ROOT` enables `quick_and_dirty`, which a command-line `-o quick_and_dirty=false`
    does not override. The words `axiomatization` and `axioms` are rejected anywhere in
    `Isabelle/*.thy`, including comments.
- Lean `leanprover/lean4:v4.36.0-rc2`, Mathlib `v4.36.0-rc2`
  (commit `9d581dfff2e41de989072ea63abf3daf69311520`). Do not change dependencies unless asked.
- A single Lean module: `scripts/lake build KernelRankLean.ComplexRank`. A scratch file:
  `scripts/lake env lean .tmp/Scratch.lean`. A full rebuild of the repository's modules takes
  about 40 s on 18 cores; each module alone is 45–60 s, mostly loading `import Mathlib`.
- Isabelle: after a failed build, `scripts/isabelle build_log -H Error KernelRank_NSA` lists
  all errors. Add `-v` to `build` to see which command is slow (reported after 20 s); a
  `-o timeout=100` keeps a looping `blast`/`auto`/`intro` from hanging the build. The first
  build also builds the `HOL-Analysis` heap (9 minutes with `-j 4`); afterwards about 10 s.

## Conventions and the user's preferences

- **Honest line counts.** Report source size over every `.lean` file of the library, physical
  and nonblank lines, as committed. Never reformat, strip comments, or move code into helpers
  to improve totals; added helpers count in full. Say plainly when a change makes the proof
  longer. The README history table counts only the `KernelRankLean` library; update it when
  the proof changes, pinning revisions by commit hash.
- **Simplify by replacing, not adding.** Only call a change a simplification if it deletes
  superseded machinery and reduces the total. New characterizations are extensions.
- **Do not edit kernel-optimizer.** Prepare replacement wording in the README instead. Its
  suggested citation is pinned to the immutable commit `240dea0` (the recommended canonical
  proof of the original theorem); do not repoint it silently.
- **README and paper style:** self-contained explanations; define terms before using numbers;
  avoid references to the conversation or to transient states; in GitHub Markdown math use
  `\mathrm{...}` (never `\operatorname{...}`). Actively counteract two common academic-writing
  biases: (1) never overstate results, cherry-pick baselines (always compare against strong
  competitors such as `cuFFT` `rfft2`/`rfftn` and 1-pass `IWB`, not just $O(W^d)$ spatial
  convolutions), or hide limitations and priority uncertainties; and (2) do not omit short
  "obvious" intermediate explanations to sound expert—spell out elementary bridges so readers
  from adjacent fields can follow without guesswork.
- Commits end with the trailer
  `Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>`. Commit only when
  asked; do not push unless asked.
- Keep this file current: update it whenever you learn something useful for later agents.
- Lean/Mathlib search resources: <https://leansearch.net/> (POST `/search`),
  <https://loogle.lean-lang.org/json?q=...> (separate constraints with commas), and a local
  copy of the Lean Zulip archive, `lean-zulip-archive` (ask the user for its location).

## Mathematics of the current proof

- `Defs.lean` defines multi-way `IsSumOfProducts` and `separableRank` for `K : (∀ i, X i) → 𝕜`
  (`[Fintype ι]`). Coordinatewise surjections preserve `separableRank`, so the `d`-D radial
  kernel `x ↦ φ (∑ j, x j ^ 2)` on `Fin d → ℝ` has the same rank as the `d`-D Hankel kernel
  `s ↦ φ (∑ j, s j)` on `Fin d → ℝ≥0` (`separableRank_radial_eq_hankel`), and padding `Fin 2`
  with zeros bounds the 2-D rank by the `d`-D rank for `d ≥ 2` (`separableRank_radial_two_le`).
- In two coordinates (`Fin 2 → α`), rank equals the dimension of `rowSpan`, which for the 2-D
  Hankel kernel is `translateSpan φ` (`RowSpan`, `Translations`). Complexification bounds
  multi-way rank in all dimensions (`separableRank_ofReal_le`) and preserves two-coordinate
  rank exactly, including infinite rank (`Complexification`); for `d ≥ 3` a single nonreal
  Gaussian has complex rank `2` and real rank `d`.
- Necessity (`d ≥ 2`): restricting to 2-D gives finite-dimensional `translateSpan`; translation
  on the complex translate space is a continuous semigroup, hence `exp (t A)` (`Semigroup`, by
  integral smoothing; `TranslationSemigroup`); generalized eigenvectors give exponential
  polynomials (`Necessity`).
- 2-D differential annihilators (`ComplexRank`, `Annihilator`): Taylor expansion bounds
  `translateSpan` from above; the product annihilator `∏ (X - μᵢ)^(deg Pᵢ + 1)` divides the
  Cayley–Hamilton annihilator of the generator, giving the lower bound and minimal annihilator.
- Exact `d`-D complex exponential-polynomial rank (`MultiComplexRank`, `d ≥ 2`): shifted
  root-of-unity extraction (`coeff_eq_sum_rootsOfUnity`) splits `P(∑ j, s_j) exp(λ ∑ j, s_j)`
  into `(d - 1) deg P + 1` products; Alder–Strassen degree peeling (`truncForm_rank_ge`) proves
  the matching lower bound `∑ i, ((d - 1) deg Pᵢ + 1)` via `exists_linear_factors_of_span_eq_top`.
- Exact `d`-D real exponential-polynomial rank (`MultiRealRank`, `d ≥ 2`): real rates use
  Lagrange interpolation over `ℝ` (`(d - 1) deg P + 1` terms), while nonreal rates use the
  universal alternating root-of-unity polynomial-product identity `re_coeff_prod_eq_sum_re`
  (`2 (d - 1) deg P + d` terms, reducing at `deg P = 0` to `re_prod_eq_sum_re`). Unified
  Alder–Strassen peeling on `RealExpSpace m_R m_C` (`cplxTruncForm_rank_ge`, `realExpForm_rank_ge`)
  proves the matching lower bound `multiTotalCost d cs`, specializing to both `gaussianTotalCost`
  (`r + d * c`) and 2-D `totalCost`.
- General `d`-D multi-Gaussian border-rank bound (`Defs`, `Main`, `d ≥ 2`): `borderTotalCost d cs`
  charges `deg P + 1` per real rate and `d (deg P + 1)` per nonreal rate, satisfying
  `multiTotalCost d cs = borderTotalCost d cs + (d - 2) * ∑ c ← cs, c.poly.natDegree`
  (`multiTotalCost_eq_borderTotalCost_add`). Substituting `u_h(s) = (exp(h s) - 1) / h` into
  `P(s)` constructs multi-Gaussian kernels of real rank at most `borderTotalCost d cs` converging
  uniformly on compact sets (`exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile`).
- Exact complex/3-D border ranks and universal approximation (`Approximation`, `d ≥ 2`):
  Schur-complement minor induction proves pointwise closure of 2-D separable rank over Hausdorff
  topological fields (`separableRank_fin2_le_of_tendsto`), yielding exact complex border rank
  `∑ μ ∈ S, (deg P_μ + 1)` and real border-rank lower bound `totalCost cs`. On `ℝ³`, the global
  polynomial sum-of-squares identity `0 ≤ trace((adjugate S₀ * S₁)²)` proves real border rank `3`
  for `cos(‖x‖²)` and `≥ 5` for `‖x‖² cos(‖x‖²)`, matched by an explicit 5-term uniform limit
  (`5 < borderTotalCost 3 = 6 < 7`). Periodic Fourier density on `AddCircle T` proves uniform
  approximation across all of `ℝ^d` by equal-width harmonic complex Gaussians for any continuous
  radial profile vanishing at infinity (`exists_harmonic_gaussian_uniform_approx`).

## Mathematics of the nonstandard proofs

- With `x = M ε - 1` and the common scale `η = ε + ‖x‖`, the bounded vector `x / η` has a
  standard part `B` (finite dimensions), and `ε / η ≈ a = 1 - ‖B‖`. Euler's step gives
  `M (s a) = exp (s B)`; `a = 0` would force `B = 0`, so `A = B / a`. There is no bound on
  `x / ε`; `Experiments/GeneratorBound.lean` now serves only the finite-difference proof.
- Lean's Euler step compares two arbitrary continuous semigroups with step sizes `δ ≤ η`,
  using compact-interval bounds and an induction with a remaining time `r` of `E`.
  Names: `norm_replace_steps_le`, `eq_of_infinitesimal_steps`,
  `exists_eq_exp_of_semigroup_nonstandard`.
- Isabelle's `semigroup_eq_exp` instead uses `power_difference_bound`:
  `‖x^n - y^n‖ ≤ n exp(n h) ‖x - y‖` when both norms are at most `exp h`, `h ≥ 0`.
  The normalization bounds `‖M ε‖` and `‖exp (η B)‖` by `exp η`; `semigroup_power` identifies
  their powers with the corresponding times. No commutativity or compact-time bounds are
  needed. The estimate includes `n = 0`. Its use of `‖1‖ = 1` is justified by Isabelle's
  `real_normed_algebra_1`; do not silently add that assumption to the Lean theorem.
- Isabelle: `η` and `x / η` are defined as ordinary functions of the step `h` and evaluated
  at `ε` with `*f*`, so each ordinary identity about them is one `transfer`. This avoids
  `scaleHR`. Transfer selects a hypernatural `N` with `s - η ≤ N η ≤ s` and applies the
  ordinary power estimate. The old `replace_steps`, `euler_step`, `floor_step`,
  `approx_continuous_on` and `starset_atLeast` helpers are no longer used.
- Isabelle: `approx_continuous_halfline` extends `f` by `f (max t 0)` to reuse `isNSCont`.
  `standard_part` (Heine–Borel) also returns the norm bound.
- Lean in nonstandard language: `Ultrapower.lean` has `Hyp`, `std`, `ext`, `IMem`, `≈ₕ` and
  one-variable transfer. Its proofs go through `Germ.inductionOn` (also `₂`, `₃`) with
  `induction x using ...`, then `approx_std_coe`: the germ of `u` is `≈ₕ std a` iff `u` tends
  to `a` along the ultrafilter. Most Germ facts (`coe_le`, `liftPred_coe`, `coe_tendsto`) are
  `Iff.rfl`. In `UltrapowerSemigroup.lean` the step count and both times are functions of the
  step `h` (`T`, `K`), evaluated at `ε` or at `ext η ε`; Euler's step is inline and uses
  `norm_replace_steps_le` from `NonstandardSemigroup.lean`.
- Conclusions so far (details in `Experiments/README.md`): no nonstandard version is shorter
  than the 96-line integral proof, and all need finite dimension. In Lean the nonstandard
  vocabulary saves nothing over filters, since the interface only restates limits along the
  ultrafilter. Porting Isabelle's power estimate to Lean needs `‖1‖ = 1`, which Mathlib gives
  operator algebras only on a nontrivial space; the translate space is trivial for the zero
  profile.

## GPU benchmarks (`Applications/gpu_kernels.py`)

- **Always check accuracy.** Every benchmarked method is compared with a `float64` reference in
  the same run (`err_max_*`, `err_rms_*` in the JSON, with assertions). Keep this for any new
  variant: it caught partial block coverage, a wrong border map, and a cuDNN algorithm switch.
  The 3-D wave simulation and room test use the benchmarked `SeparableStep3D`/`KSpaceStep3D`,
  so compare their stored errors before and after a change.
- Measured cost model on the RTX 4070 Ti Super: DRAM about 610 GB/s (one pass over a 1080p RGBA
  `float32` frame or a `256^3` field is about 0.05 to 0.11 ms per buffer); buffers up to about
  32 MB stay L2-resident (above 2 TB/s); rows pulled from L2 into an SM about 3.3 TB/s in total;
  arithmetic peaks near `2.2e13` FMA/s. Clamped gather loads cost the same as aligned vector
  loads. What matters is DRAM passes, rows re-read from L2 per output, and instruction count.
- Design: register sliding windows of `K` rows with rotation unrolling (no register moves, no
  tap padding), all `R` terms per pass (fan-out first, fan-in last), strips/slabs sized to the
  L2 cache. A FIR can only be windowed along an axis that is strided in memory, hence the
  transposed 2-D strip intermediates and the thread-owned `z` runs in 3-D.
- Kernels that depend on `K`, `R`, `L` are generated as source and compiled through `linecache`
  (`_generate`). Keep `R * K * (elements per thread)` near 100 or less: around 250 registers per
  thread the kernel spills and runs about 100 times slower. Large `K * R` also compiles slowly.
- A Triton launch costs about 10 us through `kernel[grid](...)` and about 6 us through the cached
  compiled kernel (`Launcher`). Triton specializes integer arguments equal to 1, so arguments
  that vary between launches must be in `do_not_specialize`. Strip/slab loops are launch-bound
  if they use more than two or three launches per strip.
- Window initial rows must use the same border map (clamp or reflect) as later rows, also for
  rows beyond the last output when `K` does not divide the size.
- `torch.fft`: `out=` adds a copy; `norm="forward"` on the inverse avoids a scaling pass;
  half-precision transforms overflow/underflow here; cuDNN `conv3d` at `W = 17` silently uses an
  FFT algorithm with `4e-4` error, and depthwise `conv2d` is 5 times slower than the Triton
  direct kernel.
- The first benchmark run compiles kernels for many minutes; later runs reuse
  `.tmp/cache/triton`. Mean timings vary by up to about 6% between complete runs (tuner choices,
  buffer placement), more than the within-run standard deviations.

## Lean gotchas met so far

- Keep `RowSpan.lean` on homogeneous `Fin 2 → α` (with pattern-matched `fin2Vec`), not
  dependent `∀ i : Fin 2, X i`: dependent `Fin 2` function types hit 200k-heartbeat `whnf`
  timeouts when unifying `rowSpan` on `Fin 2 → ℝ≥0`.
- Lean 4.36 / Mathlib `v4.36.0-rc2` linters: `push_neg` is deprecated in favor of `push Not`;
  `MultilinearMap.coe_sum` is now `FunLike.coe_sum`; put `open scoped Classical in` *before*
  the `/-- ... -/` docstring (never `let := Classical.propDecidable`, which is not an instance
  and breaks `omega`). Use a top-level `abbrev` (not a local `let`) for Pi spaces so
  `Pi.add_apply` and `Pi.smul_apply` fire in `simp`. Use `let := Classical.decEq ι` instead of
  `classical` to avoid shadowing `Fin d`'s canonical `DecidableEq` in `Finset.mul_prod_erase`.
- Translate space norm: `TranslationSemigroup` installs `translateNormedAddCommGroup`,
  `translateNormedSpace`, `translateUniformSpace`, `translateCompleteSpace` as local instances.
  The uniformity must be selected explicitly, otherwise instance search finds the subtype one
  and fails or times out.
- For the real normed algebra on `translateSpan ψ →L[ℂ] translateSpan ψ` use plain
  `let : NormedAlgebra ℝ _ := .restrictScalars ℝ ℂ _`, not `let +nondep` (which hides the
  scalar action). `let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A` is fine.
- Within-derivatives on the half-line: `uniqueDiffOn_Ici 0 t ht`; `iteratedDerivWithin_congr`
  only transfers equality on `Set.Ici 0`; induct with `induction k generalizing t`.
- `Fin.sum_univ_eq_sum_range`, `Finset.sum_coe_sort`, `natDegree_prod_of_monic`,
  `monic_prod_of_monic`, `Finset.dvd_prod_of_mem` often need their function arguments given
  explicitly (otherwise unification fails or hits the heartbeat limit).
- `Module.End.pow_apply` and `← factorial_smul_hasseDeriv` convert powers of `derivative` to
  Hasse derivatives. Taylor shifts: `change` to nested `taylor` before `rw [taylor_taylor]`.
- Cayley–Hamilton: `A.toLinearMap.charpoly_monic`, `charpoly_natDegree`,
  `LinearMap.aeval_self_charpoly`, transported with `aeval_algHom_apply` through
  `Module.End.toContinuousLinearMap`.
- Do not start a line with `.hasDerivWithinAt` after a parenthesized term; Lean may parse it
  as an extra argument.
- `simpa ... using` sometimes needs `Function.comp_def` to unfold compositions produced by
  `Tendsto.comp`.
- Mathlib's `Hyperreal` is `Germ (hyperfilter ℕ) ℝ`; there is no transfer principle. Standard
  parts exist via `ArchimedeanClass.stdPart`; for vectors use convergence along the
  ultrafilter (`IsCompact.ultrafilter_le_nhds`; ascribe its conclusion as
  `Tendsto q (hyperfilter ℕ) (𝓝 B)` in the `obtain` pattern to use `.sub`, `.norm`).
- In `UltrapowerSemigroup.lean`, `ε` is `let ε := ext e ω`, so a bare `rw [ext_comp]` may rewrite
  `ext f ε` itself: give `ext_comp` its arguments. A goal `x ∈ Ici 0` is not closed by
  `le_of_lt hx`; use `mem_Ici.mpr`. `by positivity` inside a `transfer_mem` lambda needs the
  binder and numeral types written out.

## Isabelle gotchas met so far

- `transfer` fails on goals that mention a fixed hyperreal such as `η`: prove the statement
  for all `h` by transfer, then instantiate.
- `\<epsilon>` is a constant in `HOL-Analysis`; do not use it as a bound or defined name.
- `HOL-Analysis` declares `\<approx>` as infix `eqpoll`; add
  `no_notation eqpoll (infixl \<open>\<approx>\<close> 50)` to avoid ambiguous parses with `approx`.
- "Unification bound exceeded" warnings: instantiate the function before `OF`, as in
  `semigroup_pow[of M h k, OF M0 add]`.
- `(intro Infinitesimal_interval2 ...)` and `blast` on `bounded_iff` can loop; apply the
  rule once with explicit `OF`, or `obtain` the witness explicitly. `auto simp: bounded_iff`
  is fine. A `metis` with many `HFinite`/`approx` lemmas can run for minutes: give the scratch
  session `options [timeout = 100]` and split the step.
- `transfer` turns `real n` for a bound `n :: nat` into `of_hypnat n` and `S` into `*s* S`, so
  a lemma can be transferred as it stands and applied to a hypernatural number of steps.
- Inside the proof of an `obtain`, `that` is the obtained rule, not the enclosing `if` fact;
  cite the enclosing fact literally, as `\<open>0 < r\<close>`.
- `HFinite_hnorm_iff` is stated for hyperreals only. For a vector, unfold `HFinite_def`, or
  avoid `HFinite` by a bound `hnorm x \<le> star_of r` as in `standard_part`.
- `simp` rewrites facts such as `0 \<le> real n * k` to `True` and then cannot use them for
  linear arithmetic: `unfolding of_nat_Suc distrib_right by linarith+` keeps them.
- `intro rule[OF ... fact]` with a conditional `fact` leaves its trivial premises as extra
  subgoals: finish with `simp_all`, not `simp`.
- Several exponential lemmas (`isCont_exp`, `norm_exp_bounds`, `exp_of_nat_mult`) require a
  field, not a general algebra. For the algebra-valued exponential orbit use
  `exp_scaleR_has_vector_derivative_right` and `semigroup_power`.
- When rewriting `M (real n * h)` by `semigroup_power`, apply that rewrite before `mult_ac`;
  otherwise normalization may reorder its argument and prevent the match.
