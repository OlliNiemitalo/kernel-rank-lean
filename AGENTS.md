# Notes for agents working on kernel-rank-lean

## Repository layout

- `KernelRankLean/` and `KernelRankLean.lean`: the proof of the separable-rank theorem for
  circularly symmetric kernels (`KernelRank.separableRank_radial_eq_iff` in `Main.lean`). It
  must stay free of `sorry`; its axioms are only `propext`, `Classical.choice`, `Quot.sound`.
- `Experiments/` and `Experiments.lean`: alternative proofs of the semigroup step
  (finite differences, nonstandard analysis) and `NonstandardDraft.lean`, a draft whose 17
  interface lemmas are deliberately `sorry`. Built by default (`lakefile.toml`).
- `Isabelle/`: an Isabelle/HOL version of the nonstandard semigroup proof (session
  `KernelRank_NSA`, theory `Semigroup_NSA.thy`), described in the README under "Alternative
  proofs of the semigroup step".
- `scripts/`: tool wrappers, setup and the check script; `.githooks/`: the pre-commit hook.
- `README.md`: theorem statement, file table, commit history with Lean line counts, the
  alternative proofs, the purely nonstandard approach, and the suggested kernel-optimizer
  citation.

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
  - `lean`: `lake exe cache get`, `lake build` (both libraries), no `sorry` outside
    `Experiments/NonstandardDraft.lean`, and `#print axioms` on the main theorems
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
- **README style:** self-contained explanations; define terms before using numbers; avoid
  references to the conversation or to transient states.
- Commits end with the trailer
  `Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>`. Commit only when
  asked; do not push unless asked.
- Keep this file current: update it whenever you learn something useful for later agents.
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

## Isabelle gotchas met so far

- `transfer` fails on goals that mention a fixed hyperreal such as `η`: prove the statement
  for all `h` by transfer, then instantiate.
- `\<epsilon>` is a constant in `HOL-Analysis`; do not use it as a bound or defined name.
- `HOL-Analysis` declares `\<approx>` as infix `eqpoll`; add
  `no_notation eqpoll (infixl \<open>\<approx>\<close> 50)` to avoid ambiguous parses with `approx`.
- "Unification bound exceeded" warnings: instantiate the function before `OF`, as in
  `semigroup_pow[of M h k, OF M0 add]`.
- `(intro Infinitesimal_interval2 ...)` and `blast` on `bounded_iff` can loop; apply the
  rule once with explicit `OF`, or `obtain` the witness explicitly.
