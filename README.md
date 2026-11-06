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

## Files

| File | Content |
|---|---|
| `Defs.lean` | Separable rank, components, representations |
| `RowSpan.lean` | Separable rank = dimension of the span of the rows |
| `Translations.lean` | For radial kernels: the span of the translates `u ↦ φ (u + t)` |
| `ProductRank.lean` | Sums of products with independent factors |
| `ExpPoly.lean`, `RealExpPoly.lean` | Uniqueness of exponential polynomials; injective real coefficient synthesis |
| `Sufficiency.lean` | A representation's kernel has rank equal to its cost |
| `Semigroup.lean` | Continuous one-parameter semigroups in a Banach algebra are `exp (t A)` |
| `Representation.lean` | Regrouping a real exponential-polynomial sum by conjugate pairs |
| `Necessity.lean` | A finite-rank radial kernel's profile is a sum of components |
| `Main.lean` | The main theorems |

## Building

```
lake exe cache get
lake build
```