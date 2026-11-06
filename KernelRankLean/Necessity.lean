import KernelRankLean.TranslationSemigroup
import KernelRankLean.Representation

/-!
# Necessity: a finite-rank radial kernel has a profile made of components

Let the translates `u ↦ φ (u + t)` of a profile `φ`, continuous on `[0, ∞)`, span a
finite-dimensional space `W` of functions on `[0, ∞)`.

* Complexification preserves the dimension of `W`.
* The shared translation realization acts on `W` itself, without coordinates, and gives
  translation by `t` as `exp (t A)`.
* Evaluation at zero reads the profile from the orbit of its initial vector. Splitting that
  vector into generalized eigenvectors of `A` gives exponentials times polynomials.
* Conjugate pairing then regroups the sum into components.
-/

open Complex Polynomial NNReal

namespace KernelRank

attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace

/-! ### Exponentials on generalized eigenvectors -/

section Exp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- On a generalized eigenvector with eigenvalue `μ`, `exp (t A)` acts as `exp (μ t)` times a
polynomial in `t`. -/
lemma exp_smul_apply_of_genEigen (A : E →L[ℂ] E) (μ : ℂ) {v : E} {k : ℕ}
    (hv : ((A.toLinearMap - μ • 1) ^ k) v = 0) (t : ℂ) :
    NormedSpace.exp (t • A) v = ∑ m ∈ Finset.range k,
      (Complex.exp (μ * t) * ((m.factorial : ℂ)⁻¹ * t ^ m)) • ((A - μ • 1) ^ m) v := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  let N := A - μ • (1 : E →L[ℂ] E)
  let L := ContinuousLinearMap.apply ℂ E v
  have hv' : (N ^ k) v = 0 := by
    change (N ^ k).toLinearMap v = 0
    simpa only [N, ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one] using hv
  have hsplit : t • A = algebraMap ℂ (E →L[ℂ] E) (μ * t) + t • N := by
    simp only [N, Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]
    rw [mul_comm t μ]
    abel
  -- The exponential series of the nilpotent part stops after `k` terms.
  have hseries := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • N)).map
    L.toLinearMap.toAddMonoidHom L.continuous
  have hterm : ∀ m, L ((m.factorial⁻¹ : ℂ) • (t • N) ^ m) =
      ((m.factorial : ℂ)⁻¹ * t ^ m) • (N ^ m) v := by
    intro m
    change (((m.factorial⁻¹ : ℂ) • (t • N) ^ m) v) = _
    simp [_root_.smul_pow, smul_smul]
  have hfin : HasSum (fun m => L
      ((m.factorial⁻¹ : ℂ) • (t • N) ^ m))
      (∑ m ∈ Finset.range k, ((m.factorial : ℂ)⁻¹ * t ^ m) • (N ^ m) v) := by
    simp only [hterm]
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    rw [Finset.mem_range, not_lt] at hm
    have hzero : (N ^ m) v = 0 := by
      rw [← Nat.sub_add_cancel hm, pow_add, mul_apply_eq_comp, hv', map_zero]
    rw [hzero, smul_zero]
  have hexpN := hseries.unique hfin
  rw [hsplit, NormedSpace.exp_add_of_commute (Algebra.commutes _ _),
    ← NormedSpace.algebraMap_exp_comm, Algebra.algebraMap_eq_smul_one,
    mul_apply_eq_comp, smul_apply, one_apply_eq_self, ← Complex.exp_eq_exp_ℂ]
  change Complex.exp (μ * t) • L (NormedSpace.exp (t • N)) = _
  refine (congrArg (Complex.exp (μ * t) • ·) hexpN).trans ?_
  rw [Finset.smul_sum]
  simp only [smul_smul, N]

/-- A continuous complex profile with finite-dimensional translate span is an exponential sum. -/
theorem exists_sum_expPoly_of_finiteDimensional (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ S : Finset ℂ, ∃ Q : ℂ → ℂ[X], ∀ t, 0 ≤ t → ψ t = ∑ μ ∈ S, expPoly (Q μ) μ t := by
  classical
  obtain ⟨A, hA⟩ := exists_translation_generator ψ hψ
  -- Split the starting vector into generalized eigenvectors.
  have hx : initialProfile ψ ∈ ⨆ μ, Module.End.maxGenEigenspace A.toLinearMap μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    trivial
  obtain ⟨f, hf, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  choose k hk using fun μ => (Module.End.mem_maxGenEigenspace _ _ _).mp (hf μ)
  let Q : ℂ → ℂ[X] := fun μ =>
    ∑ m ∈ Finset.range (k μ),
      C ((m.factorial : ℂ)⁻¹ * evalW ψ 0 (((A - μ • 1) ^ m) (f μ))) * X ^ m
  refine ⟨f.support, Q, fun t ht => ?_⟩
  rw [profile_of_generator ψ A hA ht, ← hfsum, Finsupp.sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [exp_smul_apply_of_genEigen A μ (hk μ)]
  simp only [Q, expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    map_sum, map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Necessity.** A profile, continuous on `[0, ∞)`, whose translates span a finite-dimensional
space is, on `[0, ∞)`, the profile of a representation. -/
theorem exists_representation_of_finiteDimensional (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0))
    [FiniteDimensional ℝ (translateSpan φ)] :
    ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s := by
  let ψ : ℝ → ℂ := fun t => (φ t : ℂ)
  let : FiniteDimensional ℂ (translateSpan ψ) := finiteDimensional_translateSpan_ofReal φ
  obtain ⟨S, Q, hψ⟩ := exists_sum_expPoly_of_finiteDimensional ψ
    (Complex.continuous_ofReal.comp_continuousOn hφ)
  exact exists_representation_of_sum_expPoly φ S Q hψ

end Exp

end KernelRank
