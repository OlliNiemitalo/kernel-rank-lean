import KernelRankLean.RowSpan

/-!
# Complexification preserves separable rank

Allowing complex factors does not lower the separable rank of a real-valued kernel, even on
arbitrary index sets. Real linearly independent functions remain complex linearly independent:
split any complex relation into its real and imaginary parts. Applied to a basis of the real
row span, this gives the lower bound. Conversely, every real product decomposition is also a
complex one.
-/

namespace KernelRank

variable {X Y ι : Type*}

/-- Real linearly independent functions remain independent over the complex numbers. -/
lemma linearIndependent_ofReal {f : ι → X → ℝ} (hf : LinearIndependent ℝ f) :
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

/-- A real product decomposition can be read as a complex product decomposition. -/
lemma IsSumOfProducts.ofReal {K : X → Y → ℝ} {N : ℕ} (hK : IsSumOfProducts K N) :
    IsSumOfProducts (fun x y => (K x y : ℂ)) N := by
  obtain ⟨h, v, hK⟩ := hK
  refine ⟨fun i x => (h i x : ℂ), fun i y => (v i y : ℂ), fun x y => ?_⟩
  simp only [hK, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Complexifying a real row combination gives a complex row combination. -/
lemma ofReal_mem_rowSpan {K : X → Y → ℝ} {f : X → ℝ} (hf : f ∈ rowSpan K) :
    (fun x => (f x : ℂ)) ∈ rowSpan (fun x y => (K x y : ℂ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨y, rfl⟩ := hf
    exact row_mem_rowSpan _ y
  | zero =>
    exact (rowSpan (fun x y => (K x y : ℂ))).zero_mem
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    ext x
    simp
  | smul a f _ hf =>
    convert Submodule.smul_mem (rowSpan (fun x y => (K x y : ℂ))) (a : ℂ) hf using 1
    ext x
    simp

/-- Finite-dimensionality of the complex row span implies it for the real row span. -/
lemma finiteDimensional_rowSpan_ofReal (K : X → Y → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun x y => (K x y : ℂ)))] :
    FiniteDimensional ℝ (rowSpan K) := by
  let re : rowSpan (fun x y => (K x y : ℂ)) →ₗ[ℝ] (X → ℝ) :=
    { toFun := fun f x => (f.1 x).re
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hle : rowSpan K ≤ LinearMap.range re := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨_, row_mem_rowSpan _ y⟩, by ext x; simp [re]⟩
  exact Submodule.finiteDimensional_of_le hle

/-- The real row span and the complex row span have the same finite dimension. -/
theorem finrank_rowSpan_ofReal (K : X → Y → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun x y => (K x y : ℂ)))] :
    Module.finrank ℝ (rowSpan K) =
      Module.finrank ℂ (rowSpan (fun x y => (K x y : ℂ))) := by
  let := finiteDimensional_rowSpan_ofReal K
  let b := Module.finBasis ℝ (rowSpan K)
  let v (i : Fin (Module.finrank ℝ (rowSpan K))) :
      rowSpan (fun x y => (K x y : ℂ)) :=
    ⟨fun x => ((b i : X → ℝ) x : ℂ), ofReal_mem_rowSpan (b i).2⟩
  have hb : LinearIndependent ℝ (fun i => (b i : X → ℝ)) :=
    b.linearIndependent.map' (rowSpan K).subtype (by simp)
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (rowSpan (fun x y => (K x y : ℂ))).subtype
      (linearIndependent_ofReal hb)
  refine le_antisymm ?_ ?_
  · simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
  · exact finrank_rowSpan_le_of_isSumOfProducts (isSumOfProducts_finrank_rowSpan K).ofReal

/-- Complex factors do not lower the separable rank of a real-valued kernel. -/
theorem separableRank_ofReal (K : X → Y → ℝ) :
    separableRank (fun x y => (K x y : ℂ)) = separableRank K := by
  apply le_antisymm
  · refine le_iInf₂ fun N hN => ?_
    exact iInf₂_le _ hN.ofReal
  · refine le_iInf₂ fun N hN => ?_
    let := finiteDimensional_rowSpan_of_isSumOfProducts hN
    let := finiteDimensional_rowSpan_ofReal K
    rw [separableRank_eq_finrank_rowSpan, finrank_rowSpan_ofReal]
    exact_mod_cast finrank_rowSpan_le_of_isSumOfProducts hN

end KernelRank
