import Mathlib

/-!
# Circularly symmetric kernels of finite separable rank: definitions

A 2-D convolution kernel `K x y` can be applied as a horizontal 1-D pass followed by a vertical
one when it is a product `h x * v y`. A sum of `N` such products costs `N` pairs of passes; the
least such `N` is the kernel's *separable rank*.

A circularly symmetric kernel has the form `K x y = φ (x ^ 2 + y ^ 2)` for a *profile* `φ`.
The blur demo builds profiles from *components* `s ↦ Re (P(s) · exp (λ s))`, each a polynomial
`P` times an exponential with a complex *rate* `λ = -b + i c`. A component of multiplicity
`m = deg P + 1` costs `2 m` rendering terms, or only `m` when its rate is real (`c = 0`).
-/

open Complex Polynomial

namespace KernelRank

/-- `K` is a sum of `N` products of a function of `x` and a function of `y`. -/
def IsSumOfProducts {𝕜 X Y : Type*} [CommSemiring 𝕜] (K : X → Y → 𝕜) (N : ℕ) : Prop :=
  ∃ (h : Fin N → X → 𝕜) (v : Fin N → Y → 𝕜), ∀ x y, K x y = ∑ n, h n x * v n y

/-- The separable rank of `K`: the least `N` for which `K` is a sum of `N` products,
or `⊤` if there is no such `N`. -/
noncomputable def separableRank {𝕜 X Y : Type*} [CommSemiring 𝕜] (K : X → Y → 𝕜) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : IsSumOfProducts K N), (N : ℕ∞)

/-- A component of a profile: a rate `λ` and a polynomial `P`, with values
`Re (P(s) · exp (λ s))`. -/
structure Component where
  rate : ℂ
  poly : ℂ[X]

namespace Component

/-- The component's value at `s` (the squared radius `x ^ 2 + y ^ 2` in a kernel). -/
noncomputable def eval (c : Component) (s : ℝ) : ℝ :=
  (c.poly.eval (s : ℂ) * exp (c.rate * s)).re

/-- The multiplicity `m = deg P + 1`: the number of coinciding rates the component stands for. -/
noncomputable def multiplicity (c : Component) : ℕ :=
  c.poly.natDegree + 1

/-- Rendering terms: `m` for a real rate, `2 m` for a complex one. -/
noncomputable def cost (c : Component) : ℕ :=
  if c.rate.im = 0 then c.multiplicity else 2 * c.multiplicity

/-- A well-formed component: a nonzero polynomial, a rate in the closed upper half-plane (a rate
and its conjugate give the same components), and real coefficients when the rate is real. -/
def WellFormed (c : Component) : Prop :=
  c.poly ≠ 0 ∧ 0 ≤ c.rate.im ∧ (c.rate.im = 0 → ∀ k, (c.poly.coeff k).im = 0)

end Component

/-- The profile of a list of components: the sum of their values. -/
noncomputable def profile (cs : List Component) (s : ℝ) : ℝ :=
  (cs.map fun c => c.eval s).sum

/-- The total number of rendering terms of a list of components. -/
noncomputable def totalCost (cs : List Component) : ℕ :=
  (cs.map Component.cost).sum

/-- A representation of a profile: well-formed components with distinct rates. -/
def IsRepresentation (cs : List Component) : Prop :=
  (∀ c ∈ cs, c.WellFormed) ∧ (cs.map Component.rate).Nodup

end KernelRank
