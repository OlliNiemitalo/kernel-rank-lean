import KernelRankLean.Translations
import KernelRankLean.Semigroup
import KernelRankLean.Complexification

/-!
# The exponential realization on the complex translate space

Translations act directly on the finite-dimensional span of a continuous profile's translates.
A compatible norm preserves its pointwise topology, so the translation semigroup is continuous
and has an exponential generator. The initial profile and evaluation at zero give the
realization shared by necessity and the exact-rank lower bound.
-/

open NNReal

namespace KernelRank

variable {𝕜 : Type*} [Field 𝕜]

noncomputable def shift (t : ℝ≥0) : (ℝ≥0 → 𝕜) →ₗ[𝕜] (ℝ≥0 → 𝕜) :=
  LinearMap.funLeft 𝕜 𝕜 (· + t)

lemma shift_apply (t : ℝ≥0) (g : ℝ≥0 → 𝕜) (u : ℝ≥0) : shift t g u = g (u + t) := rfl

variable (φ : ℝ → 𝕜)

lemma translate_mem_translateSpan (s : ℝ≥0) :
    (fun u : ℝ≥0 => φ (u + s)) ∈ translateSpan φ :=
  Submodule.subset_span ⟨s, rfl⟩

lemma shift_mem_translateSpan (t : ℝ≥0) {g : ℝ≥0 → 𝕜} (hg : g ∈ translateSpan φ) :
    shift t g ∈ translateSpan φ := by
  have : translateSpan φ ≤ (translateSpan φ).comap (shift t) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, rfl⟩
    refine Submodule.subset_span ⟨s + t, funext fun u => ?_⟩
    simp only [shift_apply, NNReal.coe_add]
    congr 1
    ring
  exact this hg

noncomputable def shiftW (t : ℝ≥0) : translateSpan φ →ₗ[𝕜] translateSpan φ :=
  (shift t).restrict fun _ hg => shift_mem_translateSpan φ t hg

lemma shiftW_apply (t : ℝ≥0) (g : translateSpan φ) (u : ℝ≥0) :
    (shiftW φ t g : ℝ≥0 → 𝕜) u = (g : ℝ≥0 → 𝕜) (u + t) := rfl

noncomputable def initialProfile : translateSpan φ := ⟨_, translate_mem_translateSpan φ 0⟩

lemma finiteDimensional_translateSpan_ofReal (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] :
    FiniteDimensional ℂ (translateSpan (fun t => (φ t : ℂ))) := by
  let K (u t : ℝ≥0) := φ (u + t)
  let : FiniteDimensional ℝ (rowSpan K) :=
    inferInstanceAs (FiniteDimensional ℝ (translateSpan φ))
  exact finiteDimensional_rowSpan_of_isSumOfProducts
    (isSumOfProducts_finrank_rowSpan K).ofReal

lemma finrank_translateSpan_ofReal (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] :
    Module.finrank ℂ (translateSpan (fun t => (φ t : ℂ))) =
      Module.finrank ℝ (translateSpan φ) := by
  let := finiteDimensional_translateSpan_ofReal φ
  let : FiniteDimensional ℝ (rowSpan (fun u t : ℝ≥0 => φ (u + t))) :=
    inferInstanceAs (FiniteDimensional ℝ (translateSpan φ))
  let : FiniteDimensional ℂ (rowSpan (fun u t : ℝ≥0 => (φ (u + t) : ℂ))) :=
    inferInstanceAs (FiniteDimensional ℂ (translateSpan (fun t => (φ t : ℂ))))
  exact (finrank_rowSpan_ofReal (fun u t : ℝ≥0 => φ (u + t))).symm

section Complex

variable (ψ : ℝ → ℂ) [FiniteDimensional ℂ (translateSpan ψ)]

noncomputable abbrev translateNormedAddCommGroup : NormedAddCommGroup (translateSpan ψ) := by
  let : IsNormableSpace ℂ (translateSpan ψ) := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup (translateSpan ψ) :=
    IsNormableSpace.toSeminormedAddCommGroup ℂ _
  exact NormedAddCommGroup.ofSeparation fun g hg =>
    (Metric.inseparable_iff.mpr (by simpa only [dist_zero_right] using hg)).eq

noncomputable abbrev translateNormedSpace :
    letI := translateNormedAddCommGroup ψ
    NormedSpace ℂ (translateSpan ψ) := by
  let : IsNormableSpace ℂ (translateSpan ψ) := isNormableSpace_of_finiteDimensional
  exact IsNormableSpace.toNormedSpace ℂ _

noncomputable abbrev translateUniformSpace : UniformSpace (translateSpan ψ) :=
  (translateNormedAddCommGroup ψ).toUniformSpace

attribute [local instance] translateNormedAddCommGroup translateNormedSpace translateUniformSpace

noncomputable abbrev translateCompleteSpace :
    letI := translateNormedAddCommGroup ψ
    letI := translateNormedSpace ψ
    CompleteSpace (translateSpan ψ) := FiniteDimensional.complete ℂ _

attribute [local instance] translateCompleteSpace

noncomputable def shiftCLM (t : ℝ) : translateSpan ψ →L[ℂ] translateSpan ψ :=
  (shiftW ψ t.toNNReal).toContinuousLinearMap

omit [FiniteDimensional ℂ (translateSpan ψ)] in
lemma continuous_of_mem_translateSpan (hψ : ContinuousOn ψ (Set.Ici 0))
    {g : ℝ≥0 → ℂ} (hg : g ∈ translateSpan ψ) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact hψ.comp_continuous (NNReal.continuous_coe.add continuous_const)
      fun u => Set.mem_Ici.mpr (add_nonneg u.2 s.2)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.smul hx

lemma continuous_shiftCLM (hψ : ContinuousOn ψ (Set.Ici 0)) : Continuous (shiftCLM ψ) := by
  apply continuous_clm_apply.mpr
  intro g
  apply Continuous.subtype_mk
  refine continuous_pi fun u => ?_
  exact (continuous_of_mem_translateSpan ψ hψ g.2).comp
    (continuous_const.add continuous_real_toNNReal)

lemma shiftCLM_zero : shiftCLM ψ 0 = 1 := by
  ext g u
  simp [shiftCLM, shiftW_apply]

lemma shiftCLM_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    shiftCLM ψ (s + t) = shiftCLM ψ s * shiftCLM ψ t := by
  ext g u
  simp [shiftCLM, shiftW_apply, Real.toNNReal_add hs ht, add_assoc]

noncomputable def evalW (u : ℝ≥0) : translateSpan ψ →L[ℂ] ℂ :=
  ((LinearMap.proj u).comp (translateSpan ψ).subtype).toContinuousLinearMap

lemma exists_translation_generator (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ A : translateSpan ψ →L[ℂ] translateSpan ψ,
      ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • A) := by
  let : NormedAlgebra ℝ (translateSpan ψ →L[ℂ] translateSpan ψ) :=
    .restrictScalars ℝ ℂ _
  obtain ⟨A, hA⟩ := exists_eq_exp_of_semigroup (shiftCLM ψ)
    (continuous_shiftCLM ψ hψ).continuousOn (shiftCLM_zero ψ)
    fun s t hs ht => shiftCLM_add ψ hs ht
  exact ⟨A, hA⟩

lemma generator_apply (A : translateSpan ψ →L[ℂ] translateSpan ψ)
    (hA : ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • A))
    (g : translateSpan ψ) {t : ℝ} (ht : 0 ≤ t) (u : ℝ≥0) :
    (NormedSpace.exp ((t : ℂ) • A) g).1 u = g.1 (u + t.toNNReal) := by
  rw [← hA t ht]
  rfl

lemma profile_of_generator (A : translateSpan ψ →L[ℂ] translateSpan ψ)
    (hA : ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • A))
    {t : ℝ} (ht : 0 ≤ t) :
    ψ t = evalW ψ 0 (NormedSpace.exp ((t : ℂ) • A) (initialProfile ψ)) := by
  change ψ t = (NormedSpace.exp ((t : ℂ) • A) (initialProfile ψ)).1 0
  rw [generator_apply ψ A hA _ ht]
  simp [initialProfile, Real.coe_toNNReal t ht]

end Complex

end KernelRank
