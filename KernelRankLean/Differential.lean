import KernelRankLean.TranslationSemigroup

/-!
# Differential operators on exponential orbits

Within `[0, ∞)`, differentiation of an exponential orbit applies its generator to the initial
vector. Cayley–Hamilton therefore gives every continuous finite-dimensional translate space
a monic differential annihilator of order equal to its dimension.
-/

open Polynomial NNReal

namespace KernelRank

/-- A constant-coefficient differential operator on the nonnegative half-line. -/
noncomputable def differentialOperator (p : ℂ[X]) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    p.coeff k * iteratedDerivWithin k f (Set.Ici 0) t

lemma differentialOperator_congr (q : ℂ[X]) {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator q f t = differentialOperator q g t := by
  unfold differentialOperator
  exact Finset.sum_congr rfl fun k _ => by rw [iteratedDerivWithin_congr h ht]

noncomputable section Endomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance : NormedSpace ℝ E := .restrictScalars ℝ ℂ E
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := .restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _

noncomputable def operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (t : ℝ) : ℂ :=
  β (NormedSpace.exp ((t : ℂ) • A) v)

lemma hasDerivAt_operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (t : ℝ) :
    HasDerivAt (operatorOrbit A v β) (operatorOrbit A (A v) β t) t := by
  let L := (β.comp (ContinuousLinearMap.apply ℂ E v)).restrictScalars ℝ
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const A t)

lemma iteratedDerivWithin_operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin k (operatorOrbit A v β) (Set.Ici 0) t =
      operatorOrbit A ((A ^ k) v) β t := by
  induction k generalizing t with
  | zero => simp [iteratedDerivWithin_zero]
  | succ k ih =>
    rw [iteratedDerivWithin_succ]
    have heq : Set.EqOn
        (iteratedDerivWithin k (operatorOrbit A v β) (Set.Ici 0))
        (operatorOrbit A ((A ^ k) v) β) (Set.Ici 0) := fun u hu => ih hu
    rw [derivWithin_congr heq (heq ht),
      (hasDerivAt_operatorOrbit A ((A ^ k) v) β t).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici 0 t ht), pow_succ', mul_apply_eq_comp]

lemma differentialOperator_operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (p : ℂ[X]) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator p (operatorOrbit A v β) t =
      operatorOrbit A (aeval A p v) β t := by
  simp only [differentialOperator, iteratedDerivWithin_operatorOrbit A v β _ ht]
  simp [operatorOrbit, aeval_eq_sum_range, map_sum, map_smul, smul_eq_mul]

end Endomorphism

attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace

lemma exists_charpoly_differential_annihilator (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = Module.finrank ℂ (translateSpan ψ) ∧
      ∀ t, 0 ≤ t → differentialOperator q ψ t = 0 := by
  obtain ⟨A, hA⟩ := exists_translation_generator ψ hψ
  let q := A.toLinearMap.charpoly
  have hzero : aeval A q = 0 := by
    change aeval ((Module.End.toContinuousLinearMap (translateSpan ψ)) A.toLinearMap) q = 0
    rw [aeval_algHom_apply, LinearMap.aeval_self_charpoly, map_zero]
  let v := initialProfile ψ
  let β := evalW ψ 0
  have heq : Set.EqOn ψ (operatorOrbit A v β) (Set.Ici 0) :=
    fun _ ht => profile_of_generator ψ A hA ht
  refine ⟨q, A.toLinearMap.charpoly_monic, A.toLinearMap.charpoly_natDegree, ?_⟩
  intro t ht
  rw [differentialOperator_congr q heq ht,
    differentialOperator_operatorOrbit A v β q ht, hzero]
  simp [operatorOrbit]

end KernelRank
