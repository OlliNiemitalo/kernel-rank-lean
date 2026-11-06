import Experiments.GeneratorBound

/-!
# A finite-difference proof of the continuous semigroup theorem

In a finite-dimensional real normed algebra, a semigroup `M` that is continuous on `[0, ∞)` is
`M t = exp (t A)`. The difference quotients `(M h - 1) / h` are bounded
(`exists_bounded_generators`), so a subsequence converges to some `A`. Along that subsequence,
`F x = M x * exp (-x A)` has difference quotients tending to `0` at every point. A mean-value
theorem for one-sided difference quotients then shows that `F` is constant.

This is an alternative to `KernelRank.exists_eq_exp_of_semigroup`, which smooths with an
integral instead and holds in every Banach algebra.
-/

open Filter NormedSpace Set
open scoped Topology

noncomputable section

namespace Experiments

/-- A continuous function whose difference quotients tend to `0` along one sequence of positive
steps `h n → 0`, at every point of `[0, t)`, is constant on `[0, t]`. -/
lemma constant_of_sequence_slopes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {h : ℕ → ℝ} (hpos : ∀ n, 0 < h n)
    (hz : Tendsto h atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn f (Icc 0 t))
    (hquot : ∀ x ∈ Ico 0 t,
      Tendsto (fun n => (h n)⁻¹ • (f (x + h n) - f x)) atTop (𝓝 0)) :
    f t = f 0 := by
  let g := fun x => ‖f x - f 0‖
  have hg : ContinuousOn g (Icc 0 t) := (hcont.sub continuousOn_const).norm
  have hsmall : ∀ x ∈ Ico 0 t, ∀ r : ℝ, 0 < r →
      ∃ᶠ z in 𝓝[>] x, slope g x z < r := by
    intro x hx r hr
    have hright : Tendsto (fun n => x + h n) atTop (𝓝[>] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa using tendsto_const_nhds.add hz,
        Eventually.of_forall fun n => by simpa using hpos n⟩
    have hevent : ∀ᶠ n in atTop, ‖(h n)⁻¹ • (f (x + h n) - f x)‖ < r :=
      (hquot x hx).norm.eventually (gt_mem_nhds (by simpa using hr))
    apply hright.frequently
    apply hevent.frequently.mono
    intro n hn
    calc
      slope g x (x + h n) =
          (h n)⁻¹ * (‖f (x + h n) - f 0‖ - ‖f x - f 0‖) := by
        simp [slope_def_module, g]
      _ ≤ (h n)⁻¹ * ‖f (x + h n) - f x‖ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hpos n).le)
        simpa using norm_sub_norm_le (f (x + h n) - f 0) (f x - f 0)
      _ = ‖(h n)⁻¹ • (f (x + h n) - f x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hpos n)]
      _ < r := hn
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary
    (B := fun _ => 0) (B' := fun _ => 0) hg
    (show g 0 ≤ 0 by simp [g]) continuousOn_const
    (fun x _ => (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt)
    (fun x hx r hr => hsmall x hx r hr)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (hbound ⟨ht, le_rfl⟩))

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

lemma eq_exp_of_sequence_generator (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (a : A) (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n)
    (hz : Tendsto h atTop (𝓝 0))
    (ha : Tendsto (fun n => (h n)⁻¹ • (M (h n) - 1)) atTop (𝓝 a)) :
    ∀ t, 0 ≤ t → M t = exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  intro t ht
  let F : ℝ → A := fun x => M x * exp (x • -a)
  have hFc : ContinuousOn F (Icc 0 t) := fun x hx =>
    ((hcont x hx.1).mono Icc_subset_Ici_self).mul
      (hasDerivAt_exp_smul_const (-a) x).continuousAt.continuousWithinAt
  have hFq : ∀ x ∈ Ico 0 t,
      Tendsto (fun n => (h n)⁻¹ • (F (x + h n) - F x)) atTop (𝓝 0) := by
    intro x hx
    have hright : Tendsto h atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall hpos⟩
    have hec : Tendsto (fun n => exp ((x + h n) • -a)) atTop (𝓝 (exp (x • -a))) :=
      (hasDerivAt_exp_smul_const (-a) x).continuousAt.tendsto.comp
        (by simpa using tendsto_const_nhds.add hz)
    have hed := (hasDerivAt_exp_smul_const' (-a) x).tendsto_slope_zero_right.comp hright
    have hlim := (tendsto_const_nhds (x := M x)).mul ((ha.mul hec).add hed)
    have hlim' : Tendsto
        (fun n => M x * (((h n)⁻¹ • (M (h n) - 1)) * exp ((x + h n) • -a) +
          (h n)⁻¹ • (exp ((x + h n) • -a) - exp (x • -a))))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_mul, add_neg_cancel, mul_zero] using hlim
    apply hlim'.congr'
    apply Eventually.of_forall
    intro n
    dsimp [F]
    rw [hadd x (h n) hx.1 (hpos n).le]
    simp only [smul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_add, mul_sub, mul_assoc]
    abel
  have hFt : F t = 1 := by
    rw [constant_of_sequence_slopes hpos hz ht hFc hFq]
    simp [F, h0]
  have hinv : exp (t • -a) * exp (t • a) = 1 := by
    rw [← exp_add_of_commute (((Commute.refl a).neg_left.smul_left t).smul_right t),
      smul_neg, neg_add_cancel, exp_zero]
  calc
    M t = M t * (exp (t • -a) * exp (t • a)) := by rw [hinv, mul_one]
    _ = F t * exp (t • a) := by rw [← mul_assoc]
    _ = exp (t • a) := by rw [hFt, one_mul]

/-- **Continuous semigroups are exponentials**, by finite differences and compactness. -/
theorem exists_eq_exp_of_semigroup_finiteDifference [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by
  obtain ⟨δ, hδ, C, hbound⟩ := exists_bounded_generators M (hcont 0 (by simp)) h0 hadd
  let q : ℕ → A := fun n => (δ / (n + 1 : ℝ))⁻¹ • (M (δ / (n + 1 : ℝ)) - 1)
  obtain ⟨a, _, s, hs, hlim⟩ :=
    (isCompact_closedBall (0 : A) C).tendsto_subseq
      (x := q) (fun n => by simpa [Metric.mem_closedBall, dist_eq_norm, q] using hbound n)
  let h : ℕ → ℝ := fun n => δ / (s n + 1 : ℝ)
  have hpos : ∀ n, 0 < h n := fun n => div_pos hδ (by positivity)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => (s n + 1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add_one] using
      hnat.comp ((tendsto_add_atTop_nat 1).comp hs.tendsto_atTop)
  have hz : Tendsto h atTop (𝓝 0) := by
    simpa only [h, Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_mul δ
  exact ⟨a, eq_exp_of_sequence_generator M hcont h0 hadd a h hpos hz hlim⟩

end Experiments
