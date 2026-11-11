# kernel-rank-lean

A Lean 4 / Mathlib formalization of the separable-rank theorem for circularly symmetric
blur kernels used in [kernel-optimizer](https://github.com/OlliNiemitalo/kernel-optimizer).

## The theorems

A kernel `K : (∀ i, X i) → 𝕜` on a finite family of coordinates is a sum of `N` coordinatewise
products (`IsSumOfProducts K N`) when
$K(x) = \sum_{n=0}^{N-1} \prod_i f_{n,i}(x_i)$; the least such `N` in `ℕ∞` is its *separable
rank* (`separableRank K`). On `ℝ^d` (`Fin d → ℝ`), a circularly symmetric (*radial*) kernel has
the form `x ↦ φ (∑ j, x j ^ 2)`. A *component* is `s ↦ Re (P(s) exp (λ s))` with a complex
*rate* `λ` and a nonzero polynomial `P` of degree `m - 1`, where `IsRepresentation` requires
distinct rates in the closed upper half-plane and real coefficients for real rates.

In [Main.lean](KernelRankLean/Main.lean), for `φ : ℝ → ℝ` and `ψ : ℝ → ℂ` continuous on `[0, ∞)`
and any dimension `d ≥ 2`:

1. **`d`-D finite-rank classification (`KernelRank.separableRank_radial_lt_top_iff_exists`):**
   ```lean
   separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) < ⊤ ↔
     ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s
   ```
   Restricting to a 2-D coordinate plane reduces necessity to `d = 2`; coordinatewise polynomial-
   exponential expansion gives finite `d`-way rank for every representation.

2. **Exact `d`-D complex radial rank (`KernelRank.separableRank_radial_complex_eq_iff`):**
   ```lean
   separableRank (fun x : Fin d → ℝ => ψ (∑ j, x j ^ 2)) = N ↔
     ∃ (S : Finset ℂ) (P : ℂ → ℂ[X]),
       (∀ μ ∈ S, P μ ≠ 0) ∧
       (∀ s, 0 ≤ s → ψ s = ∑ μ ∈ S, expPoly (P μ) μ s) ∧
       ∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1) = N
   ```
   A degree-`m` complex exponential polynomial `P(∑ j, s_j) exp(λ ∑ j, s_j)` splits into
   `(d - 1) m + 1` complex `d`-way products via root-of-unity interpolation on the truncated
   polynomial ring `ℂ[T] / (T^(m + 1))`, and flattened matricization together with
   Alder–Strassen substitution proves the matching lower bound (`MultiComplexRank.lean`).

3. **Exact `d`-D real multi-Gaussian rank (`KernelRank.separableRank_radial_gaussian_profile`,
   `KernelRank.separableRank_radial_gaussian_eq_iff`):** when every component has constant
   polynomial (`IsGaussianRepresentation cs`), a real rate (`Im λ = 0`) costs `1` real `d`-way
   product and a nonreal conjugate-pair rate (`Im λ > 0`) costs `d` real `d`-way products, so
   with `r` real rates and `c` nonreal rates (`gaussianTotalCost d cs = r + d * c`),
   ```lean
   separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) = gaussianTotalCost d cs
   ```
   Each nonreal Gaussian splits into `d` real `d`-way products (not `2^(d - 1)`) via the
   alternating root-of-unity identity
   $$\operatorname{Re}\!\left(\prod_{j=0}^{d-1} z_j\right) = \frac{2^{d-1}}{d}\sum_{m=0}^{d-1} (-1)^m \prod_{j=0}^{d-1} \operatorname{Re}\!\left(z_j e^{-i\pi m/d}\right),$$
   and Alder–Strassen substitution over `ℝ` proves that `r + d * c` terms are necessary
   (`MultiGaussian.lean`). In particular, for `d ≥ 3` a single nonreal Gaussian `Re(exp(i ‖x‖²))`
   has complex rank `2` (`d - 1` does not appear because `deg P = 0`, while `exp(i ‖x‖²)` and
   `exp(-i ‖x‖²)` are two complex terms) and real rank `d`, so complexification can strictly
   lower `d`-way rank in dimension three and above.

4. **Exact 2-D real radial rank (`KernelRank.separableRank_radial_eq_iff`):** in `d = 2`, a
   degree-`(m - 1)` component costs `m` terms for real `λ` and `2 m` terms for nonreal `λ`
   (`totalCost cs`), and
   ```lean
   separableRank (fun x : Fin 2 → ℝ => φ (∑ j, x j ^ 2)) = N ↔
     ∃ cs : List Component, IsRepresentation cs ∧
       (∀ s, 0 ≤ s → φ s = profile cs s) ∧ totalCost cs = N
   ```

The proof in the `KernelRankLean` library is complete (no `sorry`); `#print axioms` reports
only `propext`, `Classical.choice` and `Quot.sound`. The separate `Experiments` library and the
`Isabelle` directory hold alternative proofs of one step, also complete, described
[below](#alternative-proofs-of-the-semigroup-step).

In two coordinates (`Fin 2 → α`), separable rank equals the dimension of the row span over any
field (`RowSpan.lean`), and `separableRank_ofReal` shows that allowing complex factors does not
lower the 2-way rank of a real-valued kernel, including when its rank is infinite
(`separableRank_ofReal_le` gives the one-sided inequality in every dimension). In 2-D, the real
sufficiency proof expands each nonreal component into a conjugate pair, uses the 2-D complex
rank formula `∑ i, (deg Pᵢ + 1)`, and descends to `ℝ` by scalar extension.

`exists_minimal_differential_annihilator` gives another 2-D characterization for continuous
finite-rank profiles: there is a monic polynomial `p` whose degree equals the 2-D radial
kernel's rank, and `q(D) φ = 0` on `[0, ∞)` exactly when `p` divides `q`. Here `D` uses
derivatives within that half-line, including right derivatives at zero. For an
exponential-polynomial expansion, the proof computes
$p(X) = \prod_\mu (X - \mu)^{\deg P_\mu + 1}$.
Taylor expansion bounds the translate-span dimension from above. Cayley–Hamilton supplies
an annihilator whose degree equals that dimension, giving the matching lower bound.

Necessity and the 2-D exact-rank lower bound share one realization, with no choice of basis.
Translation acts on the finite-dimensional complex span of the translates of `φ`; it is a
continuous semigroup, hence `exp (t A)`. The profile is the initial vector, and evaluation at
zero reads it back out. Continuity uses a norm compatible with the pointwise topology.

## Files

The proof is in [KernelRankLean](KernelRankLean):

| File | Content |
|---|---|
| `Defs.lean` | Multi-way separable rank, coordinate surjections, 2-D slices, components, 2-D and `d`-D Gaussian costs |
| `RowSpan.lean` | Two-coordinate separable rank = dimension of the span of the rows |
| `Complexification.lean` | Scalar extension `ℝ → ℂ` bounds multi-way rank and preserves two-coordinate rank |
| `Translations.lean` | `d`-D radial-to-Hankel equivalence, 2-D slice bound, and `translateSpan` |
| `ExpPoly.lean`, `RealExpPoly.lean` | Uniqueness and conjugation of exponential polynomials |
| `ComplexRank.lean` | Product annihilators; 2-D complex translate-span dimension by Taylor expansion and Cayley–Hamilton |
| `Differential.lean` | Half-line differential operators; Cayley–Hamilton annihilators of exponential orbits |
| `Sufficiency.lean` | Exact 2-D real rank by conjugate expansion and scalar extension |
| `Semigroup.lean` | Continuous one-parameter semigroups in a Banach algebra are `exp (t A)` |
| `TranslationSemigroup.lean` | Shared basis-free exponential realization of translation |
| `Representation.lean` | Regrouping a real exponential-polynomial sum by conjugate pairs |
| `Necessity.lean` | A finite-rank radial kernel's profile is a sum of components |
| `Annihilator.lean` | 2-D rank equals the least constant-coefficient differential-annihilator order |
| `MultiComplexRank.lean` | Exact `d`-way complex exponential-polynomial rank `∑ i, ((d - 1) deg Pᵢ + 1)` |
| `MultiGaussian.lean` | Root-of-unity `d`-term real product identity; exact `d`-way real multi-Gaussian rank `r + d * c` |
| `Main.lean` | The `d`-D and 2-D main theorems |

Outside the proof:

| Directory | Content |
|---|---|
| [Experiments](Experiments) | Lean library: alternative proofs of the semigroup step, with their own [README](Experiments/README.md) |
| [Isabelle](Isabelle) | Isabelle/HOL session `KernelRank_NSA`: a nonstandard proof of the semigroup step |
| [scripts](scripts), [.githooks](.githooks) | Setup, tool wrappers, and the checks run before each commit |

## Commit history and Lean source size

These counts include **every `.lean` file of the `KernelRankLean` library**, including its root
import module and all helper modules. The separate `Experiments` library (see
[below](#alternative-proofs-of-the-semigroup-step)) is not part of the proof and is counted
separately, in its own README. Physical lines include comments and blank lines;
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
| This revision | Extend to `d` dimensions (`d ≥ 2`): unified multi-way separability, exact `d`-D complex rank, and exact `d`-D real multi-Gaussian rank | 3,822 | 3,537 | +2,235 |

Deltas compare consecutive rows (the commits between `cae13d6` and this revision only touch
`Experiments` and `Isabelle`). Through `240dea0`, the 2-D proof is **30 physical lines and 25
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

This revision extends `KernelRankLean` from two coordinates to arbitrary dimension `d ≥ 2`:
[MultiComplexRank.lean](KernelRankLean/MultiComplexRank.lean) (1,008 physical lines) proves the
exact `d`-way complex exponential-polynomial rank, and
[MultiGaussian.lean](KernelRankLean/MultiGaussian.lean) (978 physical lines) proves the
alternating root-of-unity `d`-term real decomposition and the exact `d`-way real multi-Gaussian
rank `r + d * c`. Including the unified multi-way core, `KernelRankLean` grows to **3,822
physical lines and 3,537 nonblank lines** (+2,235 physical lines and +2,157 nonblank lines over
`cae13d6`); this is an extension to `d ≥ 2` and tensor CP-rank lower bounds, not a
simplification of the 2-D proof.

## Alternative proofs of the semigroup step

One step of the proof shows that a one-parameter semigroup `M`, with `M (s + t) = M s * M t`
and `M 0 = 1`, that is continuous on `[0, ∞)` is an exponential: `M t = exp (t A)`. Translation
of the profile is such a semigroup, so this step produces the generator `A`.
[Semigroup.lean](KernelRankLean/Semigroup.lean) proves it by smoothing with an integral. It
works in any Banach algebra.

[Experiments](Experiments) and [Isabelle](Isabelle) hold four other proofs of this step, all
complete and all for finite-dimensional algebras. None of them is used by the main proof.
[Experiments/README.md](Experiments/README.md) describes and compares them:

* **Finite differences.** The difference quotients `(M h - 1) / h` are bounded, so a
  subsequence converges to the generator.
* **Nonstandard analysis, after Euler.** Take an infinitesimal step `ε`. The generator is read
  off from the standard part of the change `M ε - 1`, measured on a suitable infinitesimal
  scale, and `⌊t / ε⌋` steps of `M` differ from as many steps of the exponential by an
  infinitesimal. This argument has three formalizations: in Isabelle/HOL with its nonstandard
  analysis library, in Lean with sequences along an ultrafilter, and in Lean in nonstandard
  language on a small interface.

Their sizes, with every helper counted in full:

| Proof of the semigroup step | Physical lines | Nonblank lines |
|---|---:|---:|
| Integral smoothing (used by the main proof) | 96 | 87 |
| Finite differences | 256 | 233 |
| Nonstandard, Lean, with sequences | 206 | 190 |
| Nonstandard, Lean, in nonstandard language (195 of the lines are the interface) | 399 | 344 |
| Nonstandard, Isabelle/HOL | 275 | 253 |

None is shorter than the integral proof, and none is as general, so the main proof keeps it.
The nonstandard argument is more elementary: it uses no integration, and its only estimate is
algebraic.

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

`scripts/check` checks both proofs: the Lean build, that no Lean file uses `sorry`, that the
main theorems and the alternative proofs use only the axioms `propext`,
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

`lake build` builds both the `KernelRankLean` proof and the `Experiments` library.
