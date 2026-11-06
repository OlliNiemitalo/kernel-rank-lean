import Experiments.GeneratorBound

/-!
# A nonstandard proof of the continuous semigroup theorem, after Euler

In a finite-dimensional real normed algebra, a semigroup `M` that is continuous on `[0, ∞)` is
`M t = exp (t A)`. Euler's argument, made rigorous with infinitesimals:

1. Fix a positive infinitesimal step `ε`. The difference quotient `(M ε - 1) / ε` is finite
   (`exists_bounded_generators`), so in finite dimensions it has a standard part `A`.
2. Let `F s = M s * exp (-s A)`. One step changes `F` by a factor that differs from `1` by
   `ε · (infinitesimal)`, because `(M ε - 1) / ε ≈ A` and `(exp (-ε A) - 1) / ε ≈ -A`.
3. For standard `t ≥ 0`, take `K = ⌊t / ε⌋` steps. Telescoping, `F (K ε) - 1` is a sum of `K`
   such changes, so `‖F (K ε) - 1‖ ≤ K ε · C · (infinitesimal) ≈ 0`, where `C` bounds `M` and
   `exp (-s A)` on `[0, t]`. As `K ε ≈ t`, continuity gives `F t = 1`, so `M t = exp (t A)`.

Hyperreal numbers are germs of real sequences along the ultrafilter `hyperfilter ℕ`, and the
standard part of a finite germ is its limit along that ultrafilter. Mathlib has no transfer
principle, so the proof works with those sequences directly: `x ≈ y` becomes
`Tendsto (x - y) (hyperfilter ℕ) (𝓝 0)`. Steps 2 and 3 work along any filter. Step 1 uses
that the filter is an ultrafilter: a bounded sequence in a compact set converges along it,
with no subsequence to extract.

This is an alternative to `KernelRank.exists_eq_exp_of_semigroup`, which smooths with an
integral instead and holds in every Banach algebra.
-/

open Filter NormedSpace Set
open scoped Topology

noncomputable section

namespace Experiments

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- **Euler's step.** If the positive steps `ε` are infinitesimal along `l` and the difference
quotient `(M ε - 1) / ε` has standard part `a`, then `M t = exp (t a)`. -/
lemma eq_exp_of_infinitesimal_generator (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    {ι : Type*} {l : Filter ι} [l.NeBot] (a : A) (ε : ι → ℝ) (hpos : ∀ n, 0 < ε n)
    (hz : Tendsto ε l (𝓝 0))
    (ha : Tendsto (fun n => (ε n)⁻¹ • (M (ε n) - 1)) l (𝓝 a)) {t : ℝ} (ht : 0 ≤ t) :
    M t = exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let E : ℝ → A := fun s => exp (s • -a)
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_exp_smul_const (-a) s).continuousAt
  have hEadd : ∀ s u, E (s + u) = E s * E u := fun s u => by
    simp only [E, add_smul]
    exact exp_add_of_commute (((Commute.refl (-a)).smul_left s).smul_right u)
  let F : ℝ → A := fun s => M s * E s
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hE.continuousOn (s := Icc 0 t))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, ht⟩)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 ⟨le_rfl, ht⟩)
  -- Step 2: one step multiplies `F` by `M ε * E ε`, and `(M ε * E ε - 1) / ε ≈ 0`.
  let g : ι → A := fun n => (ε n)⁻¹ • (M (ε n) * E (ε n) - 1)
  have hg : Tendsto g l (𝓝 0) := by
    have hright : Tendsto ε l (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall hpos⟩
    have hEz : Tendsto (fun n => E (ε n)) l (𝓝 1) := by
      simpa [E, Function.comp_def] using (hE.tendsto 0).comp hz
    have hEd := (hasDerivAt_exp_smul_const' (-a) 0).tendsto_slope_zero_right.comp hright
    have hlim := (ha.mul hEz).add hEd
    simp only [Function.comp_def, zero_add, zero_smul, exp_zero, mul_one,
      add_neg_cancel] at hlim
    apply hlim.congr'
    apply Eventually.of_forall
    intro n
    simp only [g, E, smul_sub, sub_mul, smul_mul_assoc, one_mul]
    abel
  have hstep : ∀ n (j : ℕ), F ((j + 1 : ℕ) * ε n) - F (j * ε n) =
      M (j * ε n) * (M (ε n) * E (ε n) - 1) * E (j * ε n) := by
    intro n j
    have hj : (0 : ℝ) ≤ j * ε n := mul_nonneg (Nat.cast_nonneg j) (hpos n).le
    simp only [F]
    rw [Nat.cast_add_one, add_one_mul, hadd _ _ hj (hpos n).le, add_comm (↑j * ε n), hEadd]
    noncomm_ring
  -- Step 3: telescoping over `K = ⌊t / ε⌋` steps.
  have hKt : ∀ n, (⌊t / ε n⌋₊ : ℝ) * ε n ≤ t := fun n =>
    (le_div_iff₀ (hpos n)).mp (Nat.floor_le (div_nonneg ht (hpos n).le))
  have htel : ∀ n, ‖F (⌊t / ε n⌋₊ * ε n) - 1‖ ≤ t * (C * D * ‖g n‖) := by
    intro n
    have hsum := Finset.sum_range_sub (fun j : ℕ => F (j * ε n)) ⌊t / ε n⌋₊
    simp only [Nat.cast_zero, zero_mul, F, E, h0, zero_smul, exp_zero, mul_one] at hsum
    have hnorm : ‖M (ε n) * E (ε n) - 1‖ = ε n * ‖g n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hpos n),
        mul_inv_cancel_left₀ (hpos n).ne']
    calc
      ‖F (⌊t / ε n⌋₊ * ε n) - 1‖
          ≤ ∑ j ∈ Finset.range ⌊t / ε n⌋₊, C * ‖M (ε n) * E (ε n) - 1‖ * D := by
        rw [show F (⌊t / ε n⌋₊ * ε n) - 1 = _ from hsum.symm]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hjt : (j : ℝ) * ε n ∈ Icc 0 t :=
          ⟨mul_nonneg (Nat.cast_nonneg j) (hpos n).le,
            (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hj).le)
              (hpos n).le).trans (hKt n)⟩
        rw [show M (j * ε n) * E (j * ε n) = F (j * ε n) from rfl,
          show M ((j + 1 : ℕ) * ε n) * E ((j + 1 : ℕ) * ε n) = F ((j + 1 : ℕ) * ε n) from rfl,
          hstep]
        exact norm_mul₃_le.trans (mul_le_mul
          (mul_le_mul_of_nonneg_right (hC _ hjt) (norm_nonneg _)) (hD _ hjt) (norm_nonneg _)
          (mul_nonneg hC0 (norm_nonneg _)))
      _ = (⌊t / ε n⌋₊ * ε n) * (C * D * ‖g n‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnorm]
        ring
      _ ≤ t * (C * D * ‖g n‖) :=
        mul_le_mul_of_nonneg_right (hKt n) (mul_nonneg (mul_nonneg hC0 hD0) (norm_nonneg _))
  -- `K ε ≈ t`, so `F t ≈ F (K ε) ≈ 1`.
  have hKlim : Tendsto (fun n => (⌊t / ε n⌋₊ : ℝ) * ε n) l (𝓝[Icc 0 t] t) := by
    have hlo : ∀ n, t - ε n ≤ (⌊t / ε n⌋₊ : ℝ) * ε n := fun n => by
      have := Nat.lt_floor_add_one (t / ε n)
      rw [div_lt_iff₀ (hpos n), add_one_mul] at this
      linarith
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n =>
      ⟨mul_nonneg (Nat.cast_nonneg _) (hpos n).le, hKt n⟩⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hz) tendsto_const_nhds hlo hKt
  have hFt : F t = 1 := by
    have h1 : Tendsto (fun n => F (⌊t / ε n⌋₊ * ε n)) l (𝓝 (F t)) :=
      (((hcont.mono Icc_subset_Ici_self).mul hE.continuousOn) t ⟨ht, le_rfl⟩).tendsto.comp
        hKlim
    have h2 : Tendsto (fun n => F (⌊t / ε n⌋₊ * ε n) - 1) l (𝓝 0) :=
      squeeze_zero_norm htel (by simpa using (hg.norm.const_mul (C * D)).const_mul t)
    exact sub_eq_zero.mp (tendsto_nhds_unique (h1.sub_const 1) h2)
  have hinv : E t * exp (t • a) = 1 := by
    rw [← exp_add_of_commute (((Commute.refl a).neg_left.smul_left t).smul_right t),
      smul_neg, neg_add_cancel, exp_zero]
  calc
    M t = M t * (E t * exp (t • a)) := by rw [hinv, mul_one]
    _ = F t * exp (t • a) := by rw [← mul_assoc]
    _ = exp (t • a) := by rw [hFt, one_mul]

/-- **Continuous semigroups are exponentials**, by Euler's infinitesimal argument. -/
theorem exists_eq_exp_of_semigroup_nonstandard [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by
  obtain ⟨δ, hδ, C, hbound⟩ := exists_bounded_generators M (hcont 0 (by simp)) h0 hadd
  -- The positive infinitesimal `ε = δ / ω`, as a sequence along `hyperfilter ℕ`.
  let ε : ℕ → ℝ := fun n => δ / (n + 1 : ℝ)
  let q : ℕ → A := fun n => (ε n)⁻¹ • (M (ε n) - 1)
  -- Step 1: the standard part of the finite quotient `q`.
  obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : A) C).ultrafilter_le_nhds
    (.map q (hyperfilter ℕ)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact mem_map.mpr (univ_mem' fun n => by simpa [q, ε] using hbound n))
  rw [Ultrafilter.coe_map] at ha
  have hz : Tendsto ε (hyperfilter ℕ) (𝓝 0) := by
    refine Tendsto.mono_left ?_ Nat.hyperfilter_le_atTop
    simpa [ε, div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  exact ⟨a, fun t ht => eq_exp_of_infinitesimal_generator M hcont h0 hadd a ε
    (fun n => div_pos hδ (by positivity)) hz ha ht⟩

end Experiments
