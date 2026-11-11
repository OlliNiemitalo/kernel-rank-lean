import KernelRankLean.RowSpan

/-!
# Complexification and two-coordinate separable rank

Every real product decomposition is also a complex one, so complexification never increases
separable rank in any dimension (`separableRank_ofReal_le`). In two coordinates (`Fin 2`),
allowing complex factors does not lower the separable rank of a real-valued kernel either, even on
arbitrary index sets: real linearly independent functions remain complex linearly independent,
which applied to a basis of the real row span gives the matching lower bound. (In three or more
coordinates, complexification can strictly lower the rank of a real-valued kernel.)
-/

namespace KernelRank

/-- Real linearly independent functions remain independent over the complex numbers. -/
lemma linearIndependent_ofReal {α ι : Type*} {f : ι → α → ℝ} (hf : LinearIndependent ℝ f) :
    LinearIndependent ℂ (fun i x => (f i x : ℂ)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hre : ∑ j ∈ s, (c j).re • f j = 0 := by
    ext x
    have := congrArg Complex.re (congrFun hc x)
    simpa [Finset.sum_apply, Complex.mul_re] using this
  have him : ∑ j ∈ s, (c j).im • f j = 0 := by
    ext x
    have := congrArg Complex.im (congrFun hc x)
    simpa [Finset.sum_apply, Complex.mul_im] using this
  exact Complex.ext ((linearIndependent_iff'.mp hf) s (fun j => (c j).re) hre i hi)
    ((linearIndependent_iff'.mp hf) s (fun j => (c j).im) him i hi)

/-- A real product decomposition can be read as a complex product decomposition, in any number of
coordinates. -/
lemma IsSumOfProducts.ofReal {ι : Type*} [Fintype ι] {X : ι → Type*} {K : (∀ i, X i) → ℝ}
    {N : ℕ} (hK : IsSumOfProducts K N) :
    IsSumOfProducts (fun x => (K x : ℂ)) N := by
  obtain ⟨f, hK⟩ := hK
  refine ⟨fun n i x => (f n i x : ℂ), fun x => ?_⟩
  simp only [hK, Complex.ofReal_sum, Complex.ofReal_prod]

/-- Complexifying never increases separable rank in any dimension. -/
theorem separableRank_ofReal_le {ι : Type*} [Fintype ι] {X : ι → Type*}
    (K : (∀ i, X i) → ℝ) :
    separableRank (fun x => (K x : ℂ)) ≤ separableRank K :=
  le_iInf₂ fun _ hN => iInf₂_le _ hN.ofReal

section TwoCoord

variable {α : Type*}

/-- Complexifying a real row combination gives a complex row combination. -/
lemma ofReal_mem_rowSpan {K : (Fin 2 → α) → ℝ} {f : α → ℝ} (hf : f ∈ rowSpan K) :
    (fun x => (f x : ℂ)) ∈ rowSpan (fun z => (K z : ℂ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨y, rfl⟩ := hf
    exact row_mem_rowSpan _ y
  | zero =>
    exact (rowSpan (fun z => (K z : ℂ))).zero_mem
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    ext x
    simp
  | smul a f _ hf =>
    convert Submodule.smul_mem (rowSpan (fun z => (K z : ℂ))) (a : ℂ) hf using 1
    ext x
    simp

/-- Finite-dimensionality of the complex row span implies it for the real row span. -/
lemma finiteDimensional_rowSpan_ofReal (K : (Fin 2 → α) → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun z => (K z : ℂ)))] :
    FiniteDimensional ℝ (rowSpan K) := by
  let re : rowSpan (fun z => (K z : ℂ)) →ₗ[ℝ] (α → ℝ) :=
    { toFun := fun f x => (f.1 x).re
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hle : rowSpan K ≤ LinearMap.range re := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨_, row_mem_rowSpan _ y⟩, by ext x; simp [re]⟩
  exact Submodule.finiteDimensional_of_le hle

/-- The real row span and the complex row span have the same finite dimension. -/
theorem finrank_rowSpan_ofReal (K : (Fin 2 → α) → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun z => (K z : ℂ)))] :
    Module.finrank ℝ (rowSpan K) =
      Module.finrank ℂ (rowSpan (fun z => (K z : ℂ))) := by
  let := finiteDimensional_rowSpan_ofReal K
  let b := Module.finBasis ℝ (rowSpan K)
  let v (i : Fin (Module.finrank ℝ (rowSpan K))) :
      rowSpan (fun z => (K z : ℂ)) :=
    ⟨fun x => ((b i : α → ℝ) x : ℂ), ofReal_mem_rowSpan (b i).2⟩
  have hb : LinearIndependent ℝ (fun i => (b i : α → ℝ)) :=
    b.linearIndependent.map' (rowSpan K).subtype (by simp)
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (rowSpan (fun z => (K z : ℂ))).subtype
      (linearIndependent_ofReal hb)
  refine le_antisymm ?_ ?_
  · simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
  · exact finrank_rowSpan_le_of_isSumOfProducts (isSumOfProducts_finrank_rowSpan K).ofReal

/-- In two coordinates, complex factors do not lower the separable rank of a real-valued kernel. -/
theorem separableRank_ofReal (K : (Fin 2 → α) → ℝ) :
    separableRank (fun z => (K z : ℂ)) = separableRank K := by
  refine le_antisymm (separableRank_ofReal_le K) ?_
  refine le_iInf₂ fun N hN => ?_
  let := finiteDimensional_rowSpan_of_isSumOfProducts hN
  let := finiteDimensional_rowSpan_ofReal K
  rw [separableRank_eq_finrank_rowSpan, finrank_rowSpan_ofReal]
  exact_mod_cast finrank_rowSpan_le_of_isSumOfProducts hN

end TwoCoord

end KernelRank
