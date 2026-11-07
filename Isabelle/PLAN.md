# Plan: an Isabelle/HOL nonstandard proof of the semigroup step

## Goal

The user asked to redo the nonstandard proof of the semigroup step in Isabelle/HOL, because
Isabelle has a mature nonstandard-analysis library (`HOL-Nonstandard_Analysis`, with a
`transfer` method), unlike Mathlib. The theorem:

> If `M : real ⇒ 'a` is continuous on `{0..}`, `M 0 = 1` and `M (s + t) = M s * M t` for
> `s, t ≥ 0`, in a finite-dimensional (Heine–Borel) real Banach algebra, then
> `∃A. ∀t ≥ 0. M t = exp (t *R A)`.

The Lean counterparts are `Experiments/NonstandardSemigroup.lean` (complete, 165 lines plus
the 124-line `GeneratorBound.lean`) and `Experiments/NonstandardDraft.lean` (17 `sorry`s in a
hand-made NSA interface). The point of the Isabelle version is to see how short and natural
the proof is when the library already provides transfer, `≈`, `st`, and nonstandard
characterizations of continuity and limits.

## Current state

- `Isabelle/ROOT`: one session, `KernelRank_NSA = "HOL-Analysis" + sessions
  "HOL-Nonstandard_Analysis"`, theory `Semigroup_NSA`. (Isabelle forbids two sessions in the
  same directory.)
- `Isabelle/Semigroup_NSA.thy`: **written but never checked by Isabelle.** It will contain
  errors. Structure:
  1. Ordinary analysis: `semigroup_pow`, `geom_telescope`, `geometric_quotient_bound`,
     `exists_bounded_quotients` (difference quotients along `δ / (n + 1)` are bounded),
     `floor_step`, `telescope_bound` (telescoping over `⌊t / h⌋` steps). These mirror
     `Experiments/GeneratorBound.lean` and `norm_telescope_le`.
  2. `HFinite_approx_star_of`: in a `heine_borel` space every finite vector has a standard
     part (the library only has `st` for `hypreal`). Proof via `compact_filter` on a `cball`
     and the free ultrafilter `𝒰` (`HFinite_FreeUltrafilterNat_iff`,
     `approx_FreeUltrafilterNat_iff`).
  3. `euler_step`: given infinitesimal `ε > 0` with `( *f* Q) ε ≈ star_of A`, shows
     `M t = exp (t *R A)` using transfer of the telescoping bound, `LIM_NSLIM` for the
     derivative of `exp (s *R -A)` at 0, `isCont_isNSCont`, and `Infinitesimal_interval2`.
  4. `semigroup_eq_exp`: `ε = ( *f* (λn. δ / Suc n)) whn`, finiteness by transfer of the
     bound, standard part from step 2, then `euler_step`.

## Attempt so far

- Isabelle2026 for Linux was installed. The main download link redirected to a host that did
  not respond; the Cambridge mirror worked:
  `https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2026_linux.tar.gz`.
  The distribution ships prebuilt `Pure` and `HOL` heaps only.
- Building the `HOL-Analysis` heap was **killed for lack of memory** after 43 minutes, on a
  machine with about 7 GB available. Plan for 16 GB or more.

## Next steps

1. Install Isabelle2026 (Linux tarball from a mirror above) and put `bin/isabelle` on `PATH`.
2. Build the parent heaps once (long, 30–60+ minutes, memory hungry):
   `isabelle build -b -j 2 HOL-Analysis HOL-Nonstandard_Analysis`.
3. Check the theory: `isabelle build -d Isabelle -v KernelRank_NSA`. For faster iteration,
   make a scratch directory outside the repository with a ROOT containing a base session
   `"Analysis_NSA" in base = "HOL-Analysis" + sessions "HOL-Nonstandard_Analysis" theories
   "HOL-Nonstandard_Analysis.Nonstandard_Analysis"`, build it with `-b`, and a dev session
   on top of it; or use Isabelle/jEdit or Isabelle/VSCode interactively, with Sledgehammer.
4. Fix the theory until it builds with no `sorry`. Places most likely to need work:
   - `transfer` goals involving `hnorm`, `*f*` of lambdas such as `λh. F (K h) - 1`, and
     `floor`/`nat` in `floor_step` after transfer;
   - `HFinite_approx_star_of`: unfolding `star_of` to `star_n (λn. a)` before
     `approx_FreeUltrafilterNat_iff`; names `FreeUltrafilterNat.proper`,
     `FreeUltrafilterNat.eventually_not_iff`;
   - `has_derivative_at` / `LIM_NSLIM` step that derives `( *f* DE) ε ≈ star_of (-A)`;
   - type classes: `exp` needs `{real_normed_algebra_1, banach}`; the main theorem also needs
     `heine_borel`.
   Keep the overall structure; simplify proofs with Sledgehammer where possible.
5. Report honestly: line counts (physical and nonblank) of `Semigroup_NSA.thy`, split into
   ordinary-analysis and nonstandard parts, compared with the Lean versions (96-line integral
   proof `KernelRankLean/Semigroup.lean`; 289-line Lean nonstandard proof). Also build times.
6. Document in `README.md`: a short subsection under "Alternative proofs of the semigroup
   step" or "A purely nonstandard approach", with how to build the Isabelle session, and add
   `Isabelle/` to the layout. Optionally add CI using the Docker image
   `makarius/isabelle:Isabelle2026` (only if build time is acceptable).
7. Commit with the co-author trailer described in `AGENTS.md`. Delete this plan or update it
   when done.

## Out of scope

Porting the whole separable-rank theorem to Isabelle; changing the Lean proof; editing
kernel-optimizer.
