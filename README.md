# kernel-rank-lean

A Lean 4 / Mathlib formalization of the separable-rank theorem for circularly symmetric
blur kernels used in [kernel-optimizer](https://github.com/OlliNiemitalo/kernel-optimizer).

## The theorem

A 2-D kernel `K x y` is a sum of `N` products `h x * v y` when it can be rendered with `N`
horizontal-plus-vertical pass pairs; the least such `N` is its *separable rank*. A circularly
symmetric kernel is `K x y = φ (x ^ 2 + y ^ 2)`. A *component* is `s ↦ Re (P(s) exp (λ s))`
with a complex *rate* `λ` and a polynomial `P` of degree `m - 1`; it costs `2 m` rendering
terms, or `m` when `λ` is real.

`KernelRank.separableRank_radial_eq_iff` ([Main.lean](KernelRankLean/Main.lean)): for `φ`
continuous on `[0, ∞)`,

```lean
separableRank (fun x y => φ (x ^ 2 + y ^ 2)) = N ↔
  ∃ cs : List Component, IsRepresentation cs ∧
    (∀ s, 0 ≤ s → φ s = profile cs s) ∧ totalCost cs = N
```

where `IsRepresentation` asks for nonzero polynomials, distinct rates in the closed upper
half-plane, and real coefficients for real rates. `separableRank_radial_lt_top_iff_exists`
states the classification on its own: the rank is finite exactly when `φ` is a sum of
components on `[0, ∞)`.

The proof in the `KernelRankLean` library is complete (no `sorry`); `#print axioms` reports
only `propext`, `Classical.choice` and `Quot.sound`. The separate `Experiments` library and the `Isabelle`
directory hold alternative proofs of one step and a draft, described
[below](#alternative-proofs-of-the-semigroup-step).

The kernel-rank definitions and row-span characterization also work over arbitrary fields and
arbitrary index sets. `separableRank_ofReal` shows that allowing complex factors does not lower
the rank of a real-valued kernel, including when its rank is infinite.

For distinct complex rates, `separableRank_sum_expPoly` gives the exact rank of
`∑ i, Pᵢ(s + t) exp (λᵢ (s + t))`: the sum of `degree(Pᵢ) + 1` for nonzero polynomials.
The real sufficiency proof expands each nonreal component into a conjugate pair and uses
this complex rank formula. Real rates contribute once and conjugate pairs twice; scalar
extension then gives the same rank over the reals.

`exists_minimal_differential_annihilator` gives another characterization for continuous
finite-rank profiles: there is a monic polynomial `p` whose degree equals the radial kernel's
rank, and `q(D) φ = 0` on `[0, ∞)` exactly when `p` divides `q`. Here `D` uses derivatives
within that half-line, including right derivatives at zero. For an exponential-polynomial
expansion, the proof computes
$p(X) = \prod_\mu (X - \mu)^{\deg P_\mu + 1}$.
Taylor expansion bounds the translate-span dimension from above. Cayley–Hamilton supplies
an annihilator whose degree equals that dimension, giving the matching lower bound.

Necessity and the exact-rank lower bound share one realization, with no choice of basis.
Translation acts on the finite-dimensional complex span of the translates of `φ`; it is a
continuous semigroup, hence `exp (t A)`. The profile is the initial vector, and evaluation at
zero reads it back out. Continuity uses a norm compatible with the pointwise topology.

## Files

The proof is in [KernelRankLean](KernelRankLean):

| File | Content |
|---|---|
| `Defs.lean` | Separable rank, components, representations |
| `RowSpan.lean` | Separable rank = dimension of the span of the rows |
| `Complexification.lean` | Real-valued kernels have the same separable rank over the real and complex numbers |
| `Translations.lean` | For radial kernels: the span of the translates `u ↦ φ (u + t)` |
| `ExpPoly.lean`, `RealExpPoly.lean` | Uniqueness and conjugation of exponential polynomials |
| `ComplexRank.lean` | Product annihilators; exact complex rank by Taylor expansion and Cayley–Hamilton |
| `Differential.lean` | Half-line differential operators; Cayley–Hamilton annihilators of exponential orbits |
| `Sufficiency.lean` | Exact real rank by conjugate expansion and scalar extension |
| `Semigroup.lean` | Continuous one-parameter semigroups in a Banach algebra are `exp (t A)` |
| `TranslationSemigroup.lean` | Shared basis-free exponential realization of translation |
| `Representation.lean` | Regrouping a real exponential-polynomial sum by conjugate pairs |
| `Necessity.lean` | A finite-rank radial kernel's profile is a sum of components |
| `Annihilator.lean` | Rank equals the least constant-coefficient differential-annihilator order |
| `Main.lean` | The main theorems |

Outside the proof:

| Directory | Content |
|---|---|
| [Experiments](Experiments) | Lean library: alternative proofs of the semigroup step and a nonstandard draft |
| [Isabelle](Isabelle) | Isabelle/HOL session `KernelRank_NSA`: a nonstandard proof of the semigroup step |
| [scripts](scripts), [.githooks](.githooks) | Setup, tool wrappers, and the checks run before each commit |

## Commit history and Lean source size

These counts include **every `.lean` file of the `KernelRankLean` library**, including its root
import module and all helper modules. The separate `Experiments` library (see
[below](#alternative-proofs-of-the-semigroup-step)) is not part of the proof and is counted
separately there. Physical lines include comments and blank lines;
nonblank lines include comments but exclude whitespace-only lines. Dependencies, build
outputs and external scratch files are excluded. Each committed revision is counted from
its Git contents, not from the current checkout.

Counts use the code as committed: no reformatting, and no removal of comments or blank lines
to improve the totals. Added abstractions count in full:
moving a proof into a helper does not itself reduce the total. Line counts describe source
size, not mathematical complexity.

| Revision | Change | Physical lines | Nonblank lines | Physical-line delta |
|---|---|---:|---:|---:|
| [`2e5ff3f`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/2e5ff3fd937e7bcd4bf1436dca334a77f64fd5ba) | Initial complete separable-rank proof | 1,370 | 1,194 | - |
| [`0d9d939`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/0d9d93961eedd646b689786514d33255fac6c711) | Simplify translation continuity and semigroup smoothing | 1,316 | 1,142 | -54 |
| [`83a404c`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/83a404c7298338065b70fdc39827671a1ec3b695) | Share real/imaginary independence through coefficient synthesis | 1,341 | 1,159 | +25 |
| [`240dea0`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/240dea077b40a8aa9ce0e90ea13d8e546614f594) | Compute exact rank over the complex numbers; use conjugate expansion and scalar extension | 1,340 | 1,169 | -1 |
| [`40bfb90`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/40bfb90deb6a25928f07083cb2085605039dfd24) | Add minimal differential annihilators and share the basis-free translation realization | 1,680 | 1,457 | +340 |
| [`cae13d6`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/cae13d6897f6ce6ef43b86129d938842b0349683) | Use product annihilators and Cayley–Hamilton; delete coefficient-synthesis and cyclic-vector machinery | 1,587 | 1,380 | -93 |

Later commits do not change the `KernelRankLean` library, so the proof stays at
1,587 lines. Deltas compare consecutive rows. Through `240dea0`, the proof is **30 physical lines and 25
nonblank lines smaller** than the initial proof. Complexification saved 110 lines in the
proof-specific parts, but its reusable infrastructure makes the whole change essentially
size-neutral: one fewer physical line and ten more nonblank lines.

The `40bfb90` stage is not a like-for-like shortening of the original theorem: it adds
the differential-annihilator characterization. That extension initially brought the total
to 1,726 physical lines; sharing the translation realization then removed 46, yielding
1,680. The intermediate 1,726-line version was not committed. The 1,680-line stage
exceeds `240dea0` by 340 physical lines, with both new modules included.

`cae13d6` removes superseded proof machinery while preserving the classification and
minimal-annihilator statements: **93 fewer physical lines and 77 fewer nonblank lines** than
`40bfb90`, counting the new differential-operator module too.
It still has **271 more physical lines than `0d9d939`** (and 247 more than `240dea0`).
Thus it reduces the extended proof, but has not yet made it smaller than the earlier
classification-only proof.

## Alternative proofs of the semigroup step

One step of the proof shows that a one-parameter semigroup `M`, with `M (s + t) = M s * M t`
and `M 0 = 1`, that is continuous on `[0, ∞)` is an exponential: `M t = exp (t A)`. Translation
of the profile is such a semigroup, so this step produces the generator `A`.
[Semigroup.lean](KernelRankLean/Semigroup.lean) proves it by smoothing with an integral. It
works in any Banach algebra.

The alternatives below work in finite-dimensional algebras. They start from the same bound: if
`M` stays within `1/2` of `1` on `[0, δ]`, geometric sums bound the difference quotients
`(M h - 1) / h` for `h = δ / n`. The Lean versions share this bound,
[GeneratorBound.lean](Experiments/GeneratorBound.lean), and
[Translation.lean](Experiments/Translation.lean) applies them to the translation semigroup.

### Finite differences

[FiniteDifferenceSemigroup.lean](Experiments/FiniteDifferenceSemigroup.lean): in finite
dimensions, a subsequence of the bounded quotients converges to some `A`. Along it, the
difference quotients of `M t * exp (-t A)` tend to `0` at every point. A mean-value theorem for
one-sided difference quotients then shows that this product is constant.

### Nonstandard analysis, after Euler

Fix a positive infinitesimal step `ε`. The quotient `(M ε - 1) / ε` is finite, so it has a
standard part `A`. Each step multiplies `M t * exp (-t A)` by a factor that differs from `1` by
`ε` times an infinitesimal. Over `⌊t / ε⌋` steps these changes add up to an infinitesimal, so
the product stays `1`. The argument has three formalizations:

* **Lean** ([NonstandardSemigroup.lean](Experiments/NonstandardSemigroup.lean)). Mathlib has
  hyperreals, as sequences along an ultrafilter, but no transfer principle, so the proof works
  with those sequences directly. The ultrafilter makes the standard part exist without
  extracting a subsequence.
* **Isabelle/HOL** ([Semigroup_NSA.thy](Isabelle/Semigroup_NSA.thy)). Isabelle's
  `HOL-Nonstandard_Analysis` library provides hyperreals and nonstandard vectors as an
  ultrapower, a `transfer` method, infinite closeness `≈`, standard parts of finite hyperreals,
  and nonstandard characterizations of limits and continuity. Transfer turns the ordinary
  bounds into statements about the infinitesimal step directly. The proof adds standard parts
  of finite vectors in finite-dimensional (Heine–Borel) spaces, which the library lacks.
* **Lean draft** ([NonstandardDraft.lean](Experiments/NonstandardDraft.lean)). The same proof
  written the way a nonstandard analyst would, against a small hand-made interface: the
  ultrapower `Hyp α` along `hyperfilter ℕ`, natural extensions `ext f`, internal membership,
  and `x ≈ₕ y` for "infinitely close". 17 interface lemmas are left as `sorry`: one-variable
  transfer, arithmetic of `≈ₕ`, standard parts in finite dimensions, continuity and
  derivatives at infinitesimal scale, and `1 / ω ≈ 0`. These are the facts a nonstandard
  analysis library would provide, and most would be short proofs about limits along the
  ultrafilter. The proof of the semigroup theorem itself (91 lines) has no `sorry`. Being a
  draft, it is built by `lake build` but its theorem depends on `sorryAx`; the main theorem
  does not.

### Comparison

All but the draft compile with no unproved steps. None is shorter than the integral proof, so
the main proof keeps it:

| Proof of the semigroup step | Files | Physical lines | Nonblank lines |
|---|---|---:|---:|
| Integral smoothing (used) | `Semigroup.lean` | 96 | 87 |
| Finite differences | `GeneratorBound.lean` + `FiniteDifferenceSemigroup.lean` | 256 | 233 |
| Nonstandard analysis, Lean | `GeneratorBound.lean` + `NonstandardSemigroup.lean` | 289 | 263 |
| Nonstandard analysis, Isabelle/HOL | `Semigroup_NSA.thy` | 302 | 283 |

The shared bound, `GeneratorBound.lean`, is 124 lines (112 nonblank) of each Lean alternative.
The two nonstandard proofs split as follows (physical / nonblank lines):

| Part | Lean | Isabelle/HOL |
|---|---:|---:|
| Headers, imports and overview | 55 / 39 | 23 / 19 |
| Ordinary analysis: bounded quotients, telescoping over `⌊t / h⌋` steps | 144 / 137 | 130 / 124 |
| Nonstandard part: standard parts, Euler's step, the theorem | 90 / 87 | 149 / 140 |
| Total | 289 / 263 | 302 / 283 |

In Isabelle the ordinary analysis is shorter, helped by library lemmas on floors and
geometric sums, but the nonstandard part is longer, mostly because it proves that finite
vectors have standard parts (39 lines); the Lean proof gets them from convergence along the
ultrafilter in Mathlib.

## A purely nonstandard approach

Nonstandard analysis suggests a different picture of the whole theorem, not just the semigroup
step: the continuous result is the standard part of a discrete one. None of it is formalized
beyond the semigroup step above.

**The theorem.** Since `x²` and `y²` range over `[0, ∞)`, the separable rank of `φ(x² + y²)` is
the rank of the kernel `φ(s + t)` on `[0, ∞)²`. Fix an infinitesimal step `ε > 0` and an
unlimited hypernatural `N`, and sample on the hyperfinite grid `0, ε, 2ε, …, Nε`: let
`aₖ = φ(kε)` and let `H` be the hyperfinite Hankel matrix `H_{jk} = a_{j+k}`. For continuous `φ`,
the separable rank is finite exactly when `rank H` is a standard natural number, and then the
two are equal. If every `(r + 1)`-minor of `φ(s + t)` vanishes, this transfers to the grid, so
`rank H ≤ r`. Conversely, a nonzero `r`-minor at standard points stays nonzero at nearby grid
points, by continuity, so `rank H ≥ r`.

**The proof.** A sequence whose Hankel matrix has finite rank satisfies a linear recurrence:
`aₖ = β Sᵏ v` for a square matrix `S` (Kronecker's theorem). `S` advances the grid by one
infinitesimal step, so it is close to the identity; write `S = 1 + εQ`. In a suitable basis,
continuity and a geometric-sum bound make `Q` finite, so it has a standard part `A`. For
standard `t`, after `n = ⌊t / ε⌋` steps, `φ(t) ≈ β Sⁿ v ≈ β exp (t A) v`, as in Euler's
derivation of the exponential function; this is the semigroup argument above. Generalized
eigenvectors of `A` then give exponential polynomials, and the exact rank is algebra.
Polynomial factors such as `t e^{μt}` appear as standard parts of combinations of nearly equal
discrete roots, which is why multiplicities enter the cost.

**Why the main proof does not use it.** Mathlib has hyperreals but no transfer principle, so
every transferred statement (ranks of hyperfinite matrices, internal spans) would need its own
proof. Kronecker's theorem for finite Hankel matrices also has boundary cases that the infinite
version avoids. The main proof gets the same realization for free: shifting acts on the span of
the translates of `φ`.

## Suggested kernel-optimizer citation

The following replacement paragraph cites the verified complex-rank proof at an immutable
revision, rather than whichever proof happens to be on `main`. It does not describe the
additional differential-annihilator characterization.

> *Machine-checked proof.* The theorem is formalized in Lean 4 with Mathlib in
> [kernel-rank-lean at commit `240dea0`](https://github.com/OlliNiemitalo/kernel-rank-lean/tree/240dea077b40a8aa9ce0e90ea13d8e546614f594)
> ([`KernelRank.separableRank_radial_eq_iff`](https://github.com/OlliNiemitalo/kernel-rank-lean/blob/240dea077b40a8aa9ce0e90ea13d8e546614f594/KernelRankLean/Main.lean)),
> with no unproved steps. In step (3), continuity uses the pointwise topology and automatic
> continuity of finite-dimensional linear maps; integral smoothing shows that the translation
> semigroup is $e^{tA}$, and generalized eigenvectors give exponential polynomials. In step (4),
> independent monomial and Hasse-derivative factor families give the exact rank over
> $\mathbb{C}$. Nonreal components are expanded into conjugate pairs, and complexification
> preserves the rank of the real-valued kernel.

That revision uses Lean `v4.36.0-rc2` and Mathlib `v4.36.0-rc2` at commit
`9d581dfff2e41de989072ea63abf3daf69311520`, recorded in its
[dependency manifest](https://github.com/OlliNiemitalo/kernel-rank-lean/blob/240dea077b40a8aa9ce0e90ea13d8e546614f594/lake-manifest.json).

## Building

The build is self-contained on Linux. From the repository root:

```
scripts/setup
scripts/check
```

`scripts/setup` installs [elan](https://github.com/leanprover/elan) (Lean) and
[Isabelle2026](https://isabelle.in.tum.de/) into the ignored `.tmp/` directory, which also holds
the Mathlib cache and all build outputs, and enables the repository's git hooks.

`scripts/check` checks both proofs: the Lean build, that `sorry` occurs only in the draft
`Experiments/NonstandardDraft.lean`, that the main theorems use only the axioms `propext`,
`Classical.choice` and `Quot.sound`, the Isabelle build, and that the Isabelle theorem uses no
oracle (such as `sorry`) and the theory adds no axioms. It records each passing check in
`.tmp/checks/`, keyed by a hash of the exact input files. The pre-commit hook runs the same
script on the staged files and repeats a check only if its inputs changed since it last passed.

The first check downloads the Mathlib cache and builds Isabelle's `HOL-Analysis` heap, which
took 9 minutes with 4 parallel jobs; after that, a full check takes under a minute.

To run the tools directly, use the wrappers, which use the installation in `.tmp/`:

```
scripts/lake build
scripts/isabelle build -d Isabelle KernelRank_NSA
```

`lake build` builds both the `KernelRankLean` proof and the `Experiments` library. The
``declaration uses `sorry` `` warnings all come from the draft.
