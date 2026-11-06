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

The proof is complete (no `sorry`); `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.

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
within that half-line, including right derivatives at zero. The proof makes the translation
realization's reachability and observability explicit and identifies `p` with the generator's
minimal polynomial. This is a reusable bridge, not a shorter replacement for the component
classification proof.

Both necessity and the annihilator characterization use the same basis-free realization on
the complex translate space: the profile is its initial vector and evaluation at zero is its
output functional. Continuity uses a norm compatible with the pointwise topology; reachability
is the defining span property, and observability is equality of functions. No translation
matrices or coordinate readback are needed.

## Files

| File | Content |
|---|---|
| `Defs.lean` | Separable rank, components, representations |
| `RowSpan.lean` | Separable rank = dimension of the span of the rows |
| `Complexification.lean` | Real-valued kernels have the same separable rank over the real and complex numbers |
| `Translations.lean` | For radial kernels: the span of the translates `u ↦ φ (u + t)` |
| `ProductRank.lean` | Sums of products with independent factors |
| `ExpPoly.lean`, `RealExpPoly.lean` | Uniqueness and conjugation of exponential polynomials |
| `ComplexRank.lean` | Exact complex rank from independent monomial and Hasse-derivative factors |
| `Sufficiency.lean` | Exact real rank by conjugate expansion and scalar extension |
| `Semigroup.lean` | Continuous one-parameter semigroups in a Banach algebra are `exp (t A)` |
| `TranslationSemigroup.lean` | Shared basis-free exponential realization; reachability and observability |
| `Representation.lean` | Regrouping a real exponential-polynomial sum by conjugate pairs |
| `Necessity.lean` | A finite-rank radial kernel's profile is a sum of components |
| `Annihilator.lean` | Cyclic generators; rank equals the least constant-coefficient differential-annihilator order |
| `Main.lean` | The main theorems |

## Commit history and Lean source size

These counts include **every repository-owned `.lean` file**, including the root import
module and all new helper modules. Physical lines include comments and blank lines;
nonblank lines include comments but exclude whitespace-only lines. Dependencies, build
outputs and external scratch files are excluded. Each committed revision is counted from
its Git contents, not from the current checkout.

Counts use the existing formatting; this documentation update does not reformat Lean code
or remove comments or blank lines to improve the totals. Added abstractions count in full:
moving a proof into a helper does not itself reduce the total. Line counts describe source
size, not mathematical complexity.

| Revision | Change | Physical lines | Nonblank lines | Physical-line delta |
|---|---|---:|---:|---:|
| [`2e5ff3f`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/2e5ff3fd937e7bcd4bf1436dca334a77f64fd5ba) | Initial complete separable-rank proof | 1,370 | 1,194 | - |
| [`0ff4980`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/0ff4980367aa57dab5e193f997d25ac215333337) | Trigger CI; no Lean changes | 1,370 | 1,194 | 0 |
| [`0d9d939`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/0d9d93961eedd646b689786514d33255fac6c711) | Simplify translation continuity and semigroup smoothing | 1,316 | 1,142 | -54 |
| [`83a404c`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/83a404c7298338065b70fdc39827671a1ec3b695) | Share real/imaginary independence through coefficient synthesis | 1,341 | 1,159 | +25 |
| [`240dea0`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/240dea077b40a8aa9ce0e90ea13d8e546614f594) | Compute exact rank over the complex numbers; use conjugate expansion and scalar extension | 1,340 | 1,169 | -1 |
| Annihilator/shared-realization stage, 2026-11-06 (this revision) | Add minimal differential annihilators and share the basis-free translation realization | 1,680 | 1,457 | +340 |

Deltas compare consecutive rows. The committed proof is **30 physical lines and 25
nonblank lines smaller** than the initial proof. Complexification saved 110 lines in the
proof-specific parts, but its reusable infrastructure makes the whole change essentially
size-neutral: one fewer physical line and ten more nonblank lines.

The annihilator/shared-realization stage is not a like-for-like shortening of the original theorem: it adds
the differential-annihilator characterization. That extension initially brought the total
to 1,726 physical lines; sharing the translation realization then removed 46, yielding
1,680. The intermediate 1,726-line version was not committed. The final total still
exceeds `240dea0` by 340 physical lines, with both new modules included.

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

```
lake exe cache get
lake build
```