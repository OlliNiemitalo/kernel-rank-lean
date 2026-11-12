import Mathlib

/-!
# Circularly symmetric kernels of finite separable rank: definitions

A `d`-dimensional convolution kernel `K (x₀, …, x_{d-1})` can be applied as a cascade of `d`
one-dimensional passes—one along each coordinate axis—when it is a coordinatewise product
`∏ i, f i (x i)`. A sum of `N` such products costs `N` pass cascades; the least such `N` is the
kernel's *separable rank* (functional tensor / CP rank).

A radially symmetric kernel has the form `K x = φ (∑ i, x i ^ 2)` for a *profile* `φ`.
Profiles of finite separable rank are built from *components* `s ↦ Re (P(s) · exp (λ s))`, each
a polynomial `P` times an exponential with a complex *rate* `λ = -b + i c`. In 2-D, a component
of multiplicity `m = deg P + 1` costs `2 m` rendering terms, or `m` when its rate is real. In
`d` dimensions (`d ≥ 2`), a pure Gaussian component (`deg P = 0`) costs `1` rendering term when
its rate is real and `d` terms when its rate is complex.
-/

open Complex Polynomial

namespace KernelRank

/-- `K` is a sum of `N` coordinatewise products of one-variable functions. -/
def IsSumOfProducts {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι] {X : ι → Type*}
    (K : (∀ i, X i) → 𝕜) (N : ℕ) : Prop :=
  ∃ f : Fin N → ∀ i, X i → 𝕜, ∀ x, K x = ∑ n, ∏ i, f n i (x i)

/-- The separable rank of `K`: the least `N` for which `K` is a sum of `N` coordinatewise
products, or `⊤` if there is no such `N`. -/
noncomputable def separableRank {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X : ι → Type*} (K : (∀ i, X i) → 𝕜) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : IsSumOfProducts K N), (N : ℕ∞)

lemma IsSumOfProducts.comp {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X Y : ι → Type*} {K : (∀ i, X i) → 𝕜} {N : ℕ} (hK : IsSumOfProducts K N)
    (g : ∀ i, Y i → X i) :
    IsSumOfProducts (fun y => K fun i => g i (y i)) N := by
  obtain ⟨f, hf⟩ := hK
  exact ⟨fun n i y => f n i (g i y), fun y => hf _⟩

lemma IsSumOfProducts.finsetSum {𝕜 : Type*} [CommSemiring 𝕜] {ι α : Type*} [Fintype ι]
    [Fintype α] {X : ι → Type*} {K : α → (∀ i, X i) → 𝕜} {N : α → ℕ}
    (hK : ∀ a, IsSumOfProducts (K a) (N a)) :
    IsSumOfProducts (fun x => ∑ a, K a x) (∑ a, N a) := by
  classical
  choose f hf using hK
  let e : (Σ a, Fin (N a)) ≃ Fin (∑ a, N a) := Fintype.equivOfCardEq (by simp)
  refine ⟨fun n i x => f (e.symm n).1 (e.symm n).2 i x, fun x => ?_⟩
  simp_rw [hf]
  exact ((e.symm.sum_comp (fun p : Σ a, Fin (N a) => ∏ i, f p.1 p.2 i (x i))).trans
    (Fintype.sum_sigma _)).symm

lemma IsSumOfProducts.add {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X : ι → Type*} {K₁ K₂ : (∀ i, X i) → 𝕜} {N₁ N₂ : ℕ}
    (h₁ : IsSumOfProducts K₁ N₁) (h₂ : IsSumOfProducts K₂ N₂) :
    IsSumOfProducts (fun x => K₁ x + K₂ x) (N₁ + N₂) := by
  let K : Bool → (∀ i, X i) → 𝕜 := fun b => cond b K₁ K₂
  let N : Bool → ℕ := fun b => cond b N₁ N₂
  have hsum := IsSumOfProducts.finsetSum (α := Bool) (K := K) (N := N) fun b => by
    cases b <;> assumption
  simpa [K, N, add_comm] using hsum

/-- Coordinatewise surjections preserve separable rank. -/
theorem separableRank_comp_surjective {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X Y : ι → Type*} (K : (∀ i, X i) → 𝕜) {g : ∀ i, Y i → X i}
    (hg : ∀ i, Function.Surjective (g i)) :
    separableRank (fun y => K fun i => g i (y i)) = separableRank K := by
  refine le_antisymm (le_iInf₂ fun N hN => iInf₂_le N (hN.comp g)) ?_
  refine le_iInf₂ fun N hN => ?_
  have hinv := hN.comp fun i => Function.surjInv (hg i)
  have heq : (fun x : ∀ i, X i => K fun i => g i (Function.surjInv (hg i) (x i))) = K := by
    funext x
    congr 1
    funext i
    exact Function.surjInv_eq (hg i) (x i)
  rw [heq] at hinv
  exact iInf₂_le N hinv

/-- Padding a 2-D vector with zeros to `d` coordinates (`d ≥ 2`). -/
def padTwo {α : Type*} [Zero α] {d : ℕ} (y : Fin 2 → α) (i : Fin d) : α :=
  if h : (i : ℕ) < 2 then y ⟨i, h⟩ else 0

/-- Restricting a `d`-variable kernel (`d ≥ 2`) to its 2-D coordinate slice cannot increase
separable rank. -/
theorem separableRank_padTwo_le {𝕜 α : Type*} [CommSemiring 𝕜] [Zero α] {d : ℕ} (hd : 2 ≤ d)
    (K : (Fin d → α) → 𝕜) :
    separableRank (fun y : Fin 2 → α => K (padTwo y)) ≤ separableRank K := by
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨f, hf⟩ := hN
  let rest : Finset (Fin d) := Finset.univ.filter fun i : Fin d => ¬ (i : ℕ) < 2
  let c (n : Fin N) : 𝕜 := ∏ i ∈ rest, f n i 0
  let g (n : Fin N) : ∀ k : Fin 2, α → 𝕜 :=
    Fin.cases (fun u => c n * f n (Fin.castLE hd 0) u)
      (fun _ u => f n (Fin.castLE hd 1) u)
  refine iInf₂_le N ⟨g, fun y => ?_⟩
  dsimp only
  rw [hf]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hsplit := (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin d => (i : ℕ) < 2) (fun i => f n i (padTwo y i))).symm
  have hrest : ∏ i ∈ rest, f n i (padTwo y i) = c n :=
    Finset.prod_congr rfl fun i hi => by
      have hi' : ¬ (i : ℕ) < 2 := (Finset.mem_filter.mp hi).2
      simp [padTwo, hi']
  have htwo : ∏ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2), f n i (padTwo y i) =
      f n (Fin.castLE hd 0) (y 0) * f n (Fin.castLE hd 1) (y 1) := by
    have hset : Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2) =
        {Fin.castLE hd 0, Fin.castLE hd 1} := by
      ext ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE, Fin.val_zero, Fin.val_one]
      omega
    have hne : Fin.castLE hd 0 ≠ Fin.castLE hd 1 := by simp [Fin.ext_iff]
    rw [hset, Finset.prod_pair hne]
    simp [padTwo, Fin.castLE]
  rw [hsplit, hrest, htwo, Fin.prod_univ_two]
  change f n (Fin.castLE hd 0) (y 0) * f n (Fin.castLE hd 1) (y 1) * c n =
    c n * f n (Fin.castLE hd 0) (y 0) * f n (Fin.castLE hd 1) (y 1)
  ring

/-- A component of a profile: a rate `λ` and a polynomial `P`, with values
`Re (P(s) · exp (λ s))`. -/
structure Component where
  rate : ℂ
  poly : ℂ[X]

namespace Component

/-- The component's value at `s` (the squared radius `∑ i, x i ^ 2` in a radial kernel). -/
noncomputable def eval (c : Component) (s : ℝ) : ℝ :=
  (c.poly.eval (s : ℂ) * exp (c.rate * s)).re

/-- The multiplicity `m = deg P + 1`: the number of coinciding rates the component stands for. -/
noncomputable def multiplicity (c : Component) : ℕ :=
  c.poly.natDegree + 1

/-- Rendering terms in 2-D: `m` for a real rate, `2 m` for a complex one. -/
noncomputable def cost (c : Component) : ℕ :=
  if c.rate.im = 0 then c.multiplicity else 2 * c.multiplicity

/-- A pure Gaussian component has a constant polynomial (`deg P = 0`). -/
def IsGaussian (c : Component) : Prop :=
  c.poly.natDegree = 0

/-- Rendering terms of a Gaussian component in `d` dimensions: `1` for a real rate, `d` for a
complex rate. -/
noncomputable def gaussianCost (d : ℕ) (c : Component) : ℕ :=
  if c.rate.im = 0 then 1 else d

/-- Rendering terms of an arbitrary component in `d` dimensions (`d ≥ 2`):
`(d - 1) * deg P + 1` for a real rate, and `2 * (d - 1) * deg P + d` for a nonreal rate. -/
noncomputable def multiCost (d : ℕ) (c : Component) : ℕ :=
  if c.rate.im = 0 then (d - 1) * c.poly.natDegree + 1
  else 2 * (d - 1) * c.poly.natDegree + d

lemma multiCost_two (c : Component) : c.multiCost 2 = c.cost := by
  unfold multiCost cost multiplicity
  split_ifs <;> omega

lemma multiCost_of_isGaussian (d : ℕ) {c : Component} (hg : c.IsGaussian) :
    c.multiCost d = c.gaussianCost d := by
  unfold IsGaussian at hg
  simp [multiCost, gaussianCost, hg]

/-- Multi-Gaussian border-rank upper bound of a component in `d` dimensions: `deg P + 1` real
Gaussians when `Im λ = 0`, and `d * (deg P + 1)` real products (from `deg P + 1` complex
Gaussians) when `Im λ ≠ 0`. -/
noncomputable def borderCost (d : ℕ) (c : Component) : ℕ :=
  if c.rate.im = 0 then c.poly.natDegree + 1 else d * (c.poly.natDegree + 1)

lemma multiCost_eq_borderCost_add {d : ℕ} (hd : 2 ≤ d) (c : Component) :
    c.multiCost d = c.borderCost d + (d - 2) * c.poly.natDegree := by
  unfold multiCost borderCost
  have hd1 : 1 ≤ d := by omega
  split_ifs <;> zify [hd, hd1] <;> ring

/-- A well-formed component: a nonzero polynomial, a rate in the closed upper half-plane (a rate
and its conjugate give the same components), and real coefficients when the rate is real. -/
def WellFormed (c : Component) : Prop :=
  c.poly ≠ 0 ∧ 0 ≤ c.rate.im ∧ (c.rate.im = 0 → ∀ k, (c.poly.coeff k).im = 0)

end Component

/-- The profile of a list of components: the sum of their values. -/
noncomputable def profile (cs : List Component) (s : ℝ) : ℝ :=
  (cs.map fun c => c.eval s).sum

/-- The total number of 2-D rendering terms of a list of components. -/
noncomputable def totalCost (cs : List Component) : ℕ :=
  (cs.map Component.cost).sum

/-- The total number of `d`-D rendering terms of a list of Gaussian components. -/
noncomputable def gaussianTotalCost (d : ℕ) (cs : List Component) : ℕ :=
  (cs.map (Component.gaussianCost d)).sum

/-- The total number of `d`-D rendering terms of a list of arbitrary components (`d ≥ 2`). -/
noncomputable def multiTotalCost (d : ℕ) (cs : List Component) : ℕ :=
  (cs.map (Component.multiCost d)).sum

/-- Total multi-Gaussian border-rank upper bound of a list of components in `d` dimensions. -/
noncomputable def borderTotalCost (d : ℕ) (cs : List Component) : ℕ :=
  (cs.map (Component.borderCost d)).sum

/-- Exact-minus-border rank gap identity (`d ≥ 2`): for every component list `cs`,
`multiTotalCost d cs = borderTotalCost d cs + (d - 2) * ∑_{c ∈ cs} deg P_c`. -/
theorem multiTotalCost_eq_borderTotalCost_add {d : ℕ} (hd : 2 ≤ d) (cs : List Component) :
    multiTotalCost d cs =
      borderTotalCost d cs + (d - 2) * (cs.map fun c => c.poly.natDegree).sum := by
  induction cs with
  | nil => simp [multiTotalCost, borderTotalCost]
  | cons c cs ih =>
    change c.multiCost d + multiTotalCost d cs =
      (c.borderCost d + borderTotalCost d cs) +
        (d - 2) * (c.poly.natDegree + (cs.map fun c => c.poly.natDegree).sum)
    rw [c.multiCost_eq_borderCost_add hd, ih]
    ring

lemma multiTotalCost_two (cs : List Component) : multiTotalCost 2 cs = totalCost cs := by
  unfold multiTotalCost totalCost
  congr 1
  exact List.map_congr_left fun c _ => c.multiCost_two

lemma multiTotalCost_of_isGaussian {d : ℕ} {cs : List Component}
    (hg : ∀ c ∈ cs, c.IsGaussian) :
    multiTotalCost d cs = gaussianTotalCost d cs := by
  unfold multiTotalCost gaussianTotalCost
  congr 1
  exact List.map_congr_left fun c hc => Component.multiCost_of_isGaussian d (hg c hc)

/-- A representation of a profile: well-formed components with distinct rates. -/
def IsRepresentation (cs : List Component) : Prop :=
  (∀ c ∈ cs, c.WellFormed) ∧ (cs.map Component.rate).Nodup

/-- A multi-Gaussian representation: a representation whose components all have constant
polynomials (`deg P = 0`). -/
def IsGaussianRepresentation (cs : List Component) : Prop :=
  IsRepresentation cs ∧ ∀ c ∈ cs, c.IsGaussian

end KernelRank
