# Notes for agents working on kernel-rank-lean

## Repository layout

- `KernelRankLean/` and `KernelRankLean.lean`: the proof of the separable-rank theorem for
  circularly symmetric kernels (`KernelRank.separableRank_radial_eq_iff` in `Main.lean`). It
  must stay free of `sorry`; its axioms are only `propext`, `Classical.choice`, `Quot.sound`.
- `Experiments/` and `Experiments.lean`: alternative proofs of the semigroup step
  (finite differences, nonstandard analysis) and `NonstandardDraft.lean`, a draft whose 17
  interface lemmas are deliberately `sorry`. Built by default (`lakefile.toml`).
- `Isabelle/`: work in progress, an Isabelle/HOL port of the nonstandard semigroup proof. See
  [Isabelle/PLAN.md](Isabelle/PLAN.md) for its state and next steps.
- `README.md`: theorem statement, file table, commit history with Lean line counts, the
  alternative proofs, the purely nonstandard approach, and the suggested kernel-optimizer
  citation.

## Toolchain and commands

- Lean `leanprover/lean4:v4.36.0-rc2`, Mathlib `v4.36.0-rc2`
  (commit `9d581dfff2e41de989072ea63abf3daf69311520`). Do not change dependencies unless asked.
- `lake exe cache get` once, then `lake build` builds both libraries. A single module:
  `lake build KernelRankLean.ComplexRank`. A scratch file: `lake env lean path/to/File.lean`.
- Each module takes roughly 45–60 s, almost all of it loading `import Mathlib`.
- Audit axioms with a scratch file that imports `KernelRankLean` (and `Experiments`) and runs
  `#print axioms` on the key theorems, e.g. `separableRank_radial_eq_iff`,
  `separableRank_radial_lt_top_iff_exists`, `exists_minimal_differential_annihilator`,
  `separableRank_sum_expPoly`, `exists_translation_generator`. Keep scratch files outside the
  repository or delete them.
- `git diff --check` before committing.

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
- **README style:** self-contained explanations; define terms before using numbers; avoid
  references to the conversation or to transient states.
- Commits end with the trailer
  `Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>`. Commit only when
  asked; do not push unless asked.
- Lean/Mathlib search resources: <https://leansearch.net/> (POST `/search`),
  <https://loogle.lean-lang.org/json?q=...> (separate constraints with commas), and a local
  copy of the Lean Zulip archive, `lean-zulip-archive` (ask the user for its location).

## Mathematics of the current proof

- Rank of `φ(x² + y²)` equals rank of the Hankel kernel `φ(s + t)` on `[0, ∞)²`, which equals
  the dimension of the span of the translates of `φ` (`RowSpan`, `Translations`).
- Complexification preserves the rank of real-valued kernels, including infinite rank
  (`Complexification`).
- Necessity: translation on the finite-dimensional complex translate space is a continuous
  semigroup, hence `exp (t A)` (`Semigroup`, by integral smoothing; `TranslationSemigroup`);
  generalized eigenvectors give exponential polynomials (`Necessity`).
- Exact complex rank (`ComplexRank`): Taylor expansion gives the upper bound; the product
  annihilator `∏ (X - μᵢ)^(deg Pᵢ + 1)` divides the Cayley–Hamilton annihilator of the
  generator, giving the lower bound. Hasse-derivative independence is still used.
- Real sufficiency expands nonreal components into conjugate pairs (`Sufficiency`).

## Lean gotchas met so far

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
  ultrafilter (`IsCompact.ultrafilter_le_nhds`).
