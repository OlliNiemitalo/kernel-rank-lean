import Mathlib

/-!
# Continuous one-parameter semigroups are exponentials

If `M : ℝ → 𝔸`, in a Banach algebra, is continuous on `[0, ∞)` with `M 0 = 1` and
`M (s + t) = M s * M t`, then `M t = exp (t A)` for some `A`.

The averages `N = ∫ s in 0..δ, M s` are close to `δ • 1`, hence invertible, for small `δ`. Since
`M t * N = ∫ s in t..t + δ, M s`, the right side shows that `M` is differentiable with
`M' t = M t * A`, `A = δ⁻¹ • (M δ - 1) * N'⁻¹`. Then `M t * exp (-t A)` has zero derivative.
-/

open NormedSpace Set

namespace KernelRank

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Continuous one-parameter semigroups are exponentials.** -/
theorem exists_eq_exp_of_semigroup (M : ℝ → 𝔸) (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ A : 𝔸, ∀ t, 0 ≤ t → M t = exp (t • A) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  -- A continuous extension to the whole line, for integrating.
  set M' : ℝ → 𝔸 := fun s => M (max s 0) with hM'
  have hM'c : Continuous M' :=
    hcont.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hM'eq : ∀ s, 0 ≤ s → M' s = M s := fun s hs => by simp [M', max_eq_left hs]
  -- A short averaging window on which `M` stays close to `1`.
  obtain ⟨δ, hδ, hclose⟩ : ∃ δ > 0, ∀ s, 0 ≤ s → s ≤ δ → ‖M s - 1‖ ≤ 1 / 2 := by
    obtain ⟨ε, hε, hball⟩ :=
      Metric.continuousWithinAt_iff.mp (hcont 0 self_mem_Ici) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun s hs hsδ => ?_⟩
    have := @hball s (mem_Ici.mpr hs) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs]; linarith)
    rw [dist_eq_norm, h0] at this
    exact this.le
  set N : 𝔸 := ∫ s in (0)..δ, M' s with hN
  -- `δ⁻¹ • N` is close to `1`, hence invertible.
  have hNclose : ‖1 - δ⁻¹ • N‖ ≤ 1 / 2 := by
    have hint : ∫ s in (0)..δ, (M' s - 1) = N - δ • 1 := by
      rw [intervalIntegral.integral_sub (hM'c.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, sub_zero]
    have hbound : ‖∫ s in (0)..δ, (M' s - 1)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le hδ.le] at hs
      rw [hM'eq s hs.1.le]
      exact hclose s hs.1.le hs.2
    rw [hint, sub_zero, abs_of_pos hδ] at hbound
    have : 1 - δ⁻¹ • N = -(δ⁻¹ • (N - δ • 1)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hδ.ne', one_smul]
      abel
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc δ⁻¹ * ‖N - δ • 1‖ ≤ δ⁻¹ * (1 / 2 * δ) := by gcongr
      _ = 1 / 2 := by field_simp
  let u : 𝔸ˣ := Units.oneSub (1 - δ⁻¹ • N) (by linarith [hNclose])
  have hu : (u : 𝔸) = δ⁻¹ • N := sub_sub_cancel 1 _
  let A : 𝔸 := δ⁻¹ • ((M δ - 1) * ↑u⁻¹)
  -- `M x * N` is the integral of `M` over `[x, x + δ]`.
  have hF : ∀ x, 0 ≤ x →
      M x * N = (∫ s in (0)..(x + δ), M' s) - ∫ s in (0)..x, M' s := by
    intro x hx
    have hcomm := (ContinuousLinearMap.mul ℝ 𝔸 (M x)).intervalIntegral_comp_comm
      (hM'c.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at hcomm
    calc M x * N = ∫ s in (0)..δ, M x * M' s := hcomm.symm
      _ = ∫ s in (0)..δ, M' (x + s) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [uIcc_of_le hδ.le] at hs
          rw [hM'eq _ (add_nonneg hx hs.1), hM'eq _ hs.1, hadd x s hx hs.1]
      _ = ∫ s in x..(x + δ), M' s := by
          rw [intervalIntegral.integral_comp_add_left, add_zero]
      _ = _ := (intervalIntegral.integral_interval_sub_left (hM'c.intervalIntegrable _ _)
          (hM'c.intervalIntegrable _ _)).symm
  have hMF : ∀ x, 0 ≤ x →
      M x = δ⁻¹ • ((∫ s in (0)..(x + δ), M' s) - ∫ s in (0)..x, M' s) * ↑u⁻¹ := by
    intro x hx
    rw [← hF x hx, ← mul_smul_comm, ← hu, mul_assoc, Units.mul_inv, mul_one]
  -- So `M` has right derivative `M t * A`.
  have hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt M (M t * A) (Ici t) t := by
    intro t ht
    have h1 : HasDerivAt (fun x => ∫ s in (0)..(x + δ), M' s) (M' (t + δ)) t :=
      (hM'c.integral_hasStrictDerivAt 0 (t + δ)).hasDerivAt.comp_add_const t δ
    have h2 := (hM'c.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hD := (((h1.sub h2).hasDerivWithinAt (s := Ici t)).const_smul δ⁻¹).mul_const
      (↑u⁻¹ : 𝔸)
    refine (hD.congr (fun x hx => hMF x (ht.trans hx)) (hMF t ht)).congr_deriv ?_
    rw [hM'eq _ (by linarith), hM'eq _ ht, hadd t δ ht hδ.le, smul_mul_assoc]
    simp only [A, mul_smul_comm]
    congr 1
    noncomm_ring
  refine ⟨A, fun t ht => ?_⟩
  -- `M x * exp (-x A)` has zero right derivative, so it stays `1`.
  set E : ℝ → 𝔸 := fun x => M x * exp (x • -A) with hE
  have hEd : ∀ x, 0 ≤ x → HasDerivWithinAt E 0 (Ici x) x := by
    intro x hx
    have he := (hasDerivAt_exp_smul_const (-A) x).hasDerivWithinAt (s := Ici x)
    have hc : Commute A (exp (x • -A)) := ((Commute.refl A).neg_right.smul_right x).exp_right
    convert (hderiv x hx).fun_mul he using 1
    rw [mul_assoc, hc.eq, mul_neg, mul_neg, add_neg_cancel]
  have hEc : ContinuousOn E (Icc 0 t) := fun x hx =>
    ((hcont x hx.1).mono Icc_subset_Ici_self).mul
      (hasDerivAt_exp_smul_const (-A) x).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hEc (fun x hx => hEd x hx.1) t ⟨ht, le_rfl⟩
  have hE0 : E 0 = 1 := by simp [E, h0]
  have hinv : exp (t • -A) * exp (t • A) = 1 := by
    rw [← exp_add_of_commute (((Commute.refl A).neg_left.smul_left t).smul_right t), smul_neg,
      neg_add_cancel, exp_zero]
  calc M t = M t * (exp (t • -A) * exp (t • A)) := by rw [hinv, mul_one]
    _ = E t * exp (t • A) := by rw [← mul_assoc]
    _ = exp (t • A) := by rw [hconst, hE0, one_mul]

end KernelRank
