import Mathlib

/-!
# Exponential polynomials vanish only trivially

If `∑ μ ∈ S, P μ (u) · exp (μ u) = 0` for all `u > 0`, with distinct rates `μ`, then every
polynomial `P μ` is zero. Proof by induction on `S`: applying `d/du - a` to the sum turns each
term `P(u) exp (μ u)` into `(P' + (μ - a) P)(u) exp (μ u)`. Applied `deg P a + 1` times, this
removes the term with rate `a`; for every other rate it is injective on polynomials, since it keeps
the leading coefficient times `μ - a ≠ 0`.
-/

open Complex Polynomial

namespace KernelRank

/-- The exponential polynomial `u ↦ P(u) · exp (μ u)` on the real line. -/
noncomputable def expPoly (P : ℂ[X]) (μ : ℂ) (u : ℝ) : ℂ :=
  P.eval (u : ℂ) * exp (μ * u)

@[simp] lemma expPoly_zero (μ : ℂ) (u : ℝ) : expPoly 0 μ u = 0 := by
  simp [expPoly]

lemma expPoly_add (P Q : ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (P + Q) μ u = expPoly P μ u + expPoly Q μ u := by
  simp [expPoly, add_mul]

lemma expPoly_C_mul (c : ℂ) (P : ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (C c * P) μ u = c * expPoly P μ u := by
  simp [expPoly, mul_assoc]

lemma hasDerivAt_expPoly (P : ℂ[X]) (μ : ℂ) (u : ℝ) :
    HasDerivAt (expPoly P μ) (expPoly (derivative P + C μ * P) μ u) u := by
  have h1 : HasDerivAt (fun u : ℝ => P.eval (u : ℂ)) ((derivative P).eval (u : ℂ)) u :=
    (P.hasDerivAt (u : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun u : ℝ => exp (μ * u)) (exp (μ * u) * μ) u := by
    have : HasDerivAt (fun u : ℝ => μ * (u : ℂ)) μ u := by
      simpa using ((hasDerivAt_id (u : ℂ)).const_mul μ).comp_ofReal
    exact this.cexp
  refine (h1.mul h2).congr_deriv ?_
  simp only [expPoly, eval_add, eval_mul, eval_C]
  ring

/-- `d/du - a` applied to `P(u) exp (μ u)` gives `shiftDeriv a μ P (u) · exp (μ u)`. -/
noncomputable def shiftDeriv (a μ : ℂ) (P : ℂ[X]) : ℂ[X] :=
  derivative P + C (μ - a) * P

/-- `d/du - a` preserves vanishing on `u > 0`. -/
lemma sum_shiftDeriv_eq_zero {S : Finset ℂ} {P : ℂ → ℂ[X]} (a : ℂ)
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) :
    ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (shiftDeriv a μ (P μ)) μ u = 0 := by
  intro u hu
  have hderiv : HasDerivAt (fun u => ∑ μ ∈ S, expPoly (P μ) μ u)
      (∑ μ ∈ S, expPoly (derivative (P μ) + C μ * P μ) μ u) u :=
    HasDerivAt.fun_sum fun μ _ => hasDerivAt_expPoly (P μ) μ u
  have hzero : HasDerivAt (fun u => ∑ μ ∈ S, expPoly (P μ) μ u) 0 u := by
    refine (hasDerivAt_const u (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hu] with v hv using h v hv
  have h0 : ∑ μ ∈ S, expPoly (derivative (P μ) + C μ * P μ) μ u = 0 := hderiv.unique hzero
  have h1 : ∑ μ ∈ S, expPoly (shiftDeriv a μ (P μ)) μ u =
      ∑ μ ∈ S, expPoly (derivative (P μ) + C μ * P μ) μ u -
        a * ∑ μ ∈ S, expPoly (P μ) μ u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have : shiftDeriv a μ (P μ) = (derivative (P μ) + C μ * P μ) + C (-a) * P μ := by
      simp only [shiftDeriv, C_sub, C_neg]
      ring
    rw [this, expPoly_add, expPoly_C_mul]
    ring
  rw [h1, h0, h u hu, mul_zero, sub_zero]

lemma iterate_sum_shiftDeriv_eq_zero {S : Finset ℂ} {P : ℂ → ℂ[X]} (a : ℂ) (n : ℕ)
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) :
    ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly ((shiftDeriv a μ)^[n] (P μ)) μ u = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact sum_shiftDeriv_eq_zero a ih

lemma shiftDeriv_self (a : ℂ) (P : ℂ[X]) : shiftDeriv a a P = derivative P := by
  simp [shiftDeriv]

/-- For `μ ≠ a`, `shiftDeriv a μ` is injective: it keeps the leading coefficient times `μ - a`. -/
lemma eq_zero_of_shiftDeriv_eq_zero {a μ : ℂ} (hμ : μ ≠ a) {P : ℂ[X]}
    (h : shiftDeriv a μ P = 0) : P = 0 := by
  by_contra hP
  have hcoeff := congrArg (fun Q => Q.coeff P.natDegree) h
  simp only [shiftDeriv, coeff_add, coeff_derivative, coeff_C_mul, coeff_zero] at hcoeff
  rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul, zero_add] at hcoeff
  exact mul_ne_zero (sub_ne_zero.mpr hμ) (leadingCoeff_ne_zero.mpr hP) hcoeff

lemma eq_zero_of_iterate_shiftDeriv_eq_zero {a μ : ℂ} (hμ : μ ≠ a) (n : ℕ) {P : ℂ[X]}
    (h : (shiftDeriv a μ)^[n] P = 0) : P = 0 := by
  induction n generalizing P with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact eq_zero_of_shiftDeriv_eq_zero hμ (ih h)

/-- A polynomial vanishing on `u > 0` is zero. -/
lemma eq_zero_of_eval_ofReal_eq_zero {P : ℂ[X]} (h : ∀ u : ℝ, 0 < u → P.eval (u : ℂ) = 0) :
    P = 0 := by
  refine eq_zero_of_infinite_isRoot P ?_
  refine Set.Infinite.mono ?_ ((Set.Ioi_infinite (0 : ℝ)).image ofReal_injective.injOn)
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

/-- **Exponential polynomials vanish only trivially**: if `∑ μ ∈ S, P μ (u) · exp (μ u) = 0` for
all `u > 0`, then `P μ = 0` for every `μ ∈ S`. -/
theorem eq_zero_of_sum_expPoly_eq_zero (S : Finset ℂ) (P : ℂ → ℂ[X])
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) : ∀ μ ∈ S, P μ = 0 := by
  induction S using Finset.induction_on generalizing P with
  | empty => simp
  | insert a S ha ih =>
    -- Remove the term with rate `a` by applying `d/du - a` enough times.
    have hQ := iterate_sum_shiftDeriv_eq_zero a ((P a).natDegree + 1) h
    have hQa : (shiftDeriv a a)^[(P a).natDegree + 1] (P a) = 0 := by
      have : shiftDeriv a a = derivative := funext (shiftDeriv_self a)
      rw [this]
      exact iterate_derivative_eq_zero (Nat.lt_succ_self _)
    simp only [Finset.sum_insert ha, hQa, expPoly_zero, zero_add] at hQ
    have hS : ∀ μ ∈ S, P μ = 0 := fun μ hμ =>
      eq_zero_of_iterate_shiftDeriv_eq_zero (by rintro rfl; exact ha hμ) _
        (ih (fun μ => (shiftDeriv a μ)^[(P a).natDegree + 1] (P μ)) hQ μ hμ)
    -- Then the remaining term `P a (u) · exp (a u)` vanishes, so `P a` has infinitely many roots.
    have ha0 : P a = 0 := by
      refine eq_zero_of_eval_ofReal_eq_zero fun u hu => ?_
      have := h u hu
      rw [Finset.sum_insert ha, Finset.sum_eq_zero fun μ hμ => by simp [hS μ hμ], add_zero,
        expPoly] at this
      exact (mul_eq_zero.mp this).resolve_right (exp_ne_zero _)
    intro μ hμ
    rcases Finset.mem_insert.mp hμ with rfl | hμ
    · exact ha0
    · exact hS μ hμ

end KernelRank
