import Mathlib

/-!
# A nonstandard proof of the continuous semigroup theorem, after Euler

In a finite-dimensional real normed algebra, a semigroup `M` that is continuous on `[0, ∞)` is
`M t = exp (t A)`. Euler's argument, made rigorous with infinitesimals:

Fix a positive infinitesimal step `ε`. In the time `ε` the semigroup changes by `x = M ε - 1`,
which is infinitesimal too. The generator should be the standard part of `x / ε`, but that
quotient might be infinite. So measure the time and the change on the common scale
`η = ε + ‖x‖` instead. As `ε / η + ‖x / η‖ = 1`, both are finite: in finite dimensions `x / η`
has a standard part `B`, and `ε / η ≈ a = 1 - ‖B‖`. The pair `(a, B)` is the generator in
homogeneous coordinates.

1. Euler's step. For `E u = exp (u B)`, the steps `M ε` and `E η` differ by `η` times an
   infinitesimal, because `(M ε - 1) / η ≈ B ≈ (E η - 1) / η`. Take `N = ⌊s / η⌋` steps, for a
   standard `s ≥ 0`. Replacing the steps of `M` by those of `E`, one at a time, changes the
   result by `N η ≤ s` times an infinitesimal. The semigroup `M` arrives at the time
   `N ε ≈ s a` and `E` at the time `N η ≈ s`, so `M (s a) = exp (s B)`.
2. The semigroup is not infinitely fast: `a = 0` would give `exp (s B) = M 0 = 1` for all
   `s ≥ 0`, so `B = 0` and `a = 1`. Hence `M t = exp (t (B / a))`.

Hyperreal numbers are germs of real sequences along the ultrafilter `hyperfilter ℕ`, and the
standard part of a finite germ is its limit along that ultrafilter. Mathlib has no transfer
principle, so the proof works with those sequences directly: `x ≈ y` becomes
`Tendsto (x - y) (hyperfilter ℕ) (𝓝 0)`. Euler's step works along any filter. The standard
part `B` uses that the filter is an ultrafilter: a bounded sequence in a compact set converges
along it, with no subsequence to extract.

This is an alternative to `KernelRank.exists_eq_exp_of_semigroup`, which smooths with an
integral instead and holds in every Banach algebra.
-/

open Filter NormedSpace Set
open scoped Topology

noncomputable section

namespace Experiments

variable {A : Type*} [NormedRing A]

/-- Let `M` take `n` steps of size `h`, followed by `E` for a time `r`. Each step of `M` can be
replaced by a step of size `k` of `E` at the cost of `C D ‖M h - E k‖`, where `C` and `D` bound
`M` and `E` on `[0, t]`. -/
lemma norm_replace_steps_le (M E : ℝ → A) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (hEadd : ∀ s t, 0 ≤ s → 0 ≤ t → E (s + t) = E s * E t) {t C D : ℝ}
    (hC : ∀ s ∈ Icc 0 t, ‖M s‖ ≤ C) (hD : ∀ s ∈ Icc 0 t, ‖E s‖ ≤ D) {h k : ℝ} (hh : 0 ≤ h)
    (hk : 0 ≤ k) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hnh : n * h ≤ t) (hnk : n * k + r ≤ t) :
    ‖M (n * h) * E r - E (n * k + r)‖ ≤ n * (C * D * ‖M h - E k‖) := by
  induction n generalizing r with
  | zero => simp [h0]
  | succ n ih =>
    have hu : 0 ≤ (n : ℝ) * h := mul_nonneg n.cast_nonneg hh
    have hv : 0 ≤ (n : ℝ) * k := mul_nonneg n.cast_nonneg hk
    rw [Nat.cast_add_one, add_one_mul] at hnh hnk
    have hut : (n : ℝ) * h ∈ Icc 0 t := ⟨hu, by linarith⟩
    have hrt : r ∈ Icc 0 t := ⟨hr, by linarith⟩
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ hut)
    have heq : M ((n + 1 : ℕ) * h) * E r - E ((n + 1 : ℕ) * k + r) =
        M (n * h) * (M h - E k) * E r + (M (n * h) * E (k + r) - E (n * k + (k + r))) := by
      rw [Nat.cast_add_one, add_one_mul, add_one_mul, hadd _ _ hu hh, hEadd _ _ hk hr, add_assoc]
      noncomm_ring
    rw [heq]
    calc
      _ ≤ ‖M (n * h) * (M h - E k) * E r‖ + ‖M (n * h) * E (k + r) - E (n * k + (k + r))‖ :=
        norm_add_le _ _
      _ ≤ C * ‖M h - E k‖ * D + n * (C * D * ‖M h - E k‖) :=
        add_le_add
          (norm_mul₃_le.trans (mul_le_mul (mul_le_mul_of_nonneg_right (hC _ hut) (norm_nonneg _))
            (hD _ hrt) (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))))
          (ih (add_nonneg hk hr) (by linarith) (by linarith))
      _ = ((n + 1 : ℕ) : ℝ) * (C * D * ‖M h - E k‖) := by
        push_cast
        ring

variable [NormedAlgebra ℝ A]

/-- **Euler's step.** Two continuous semigroups whose infinitesimal steps agree to first order
are equal, up to a change of speed. Let `M` take the steps `δ` while `E` takes the steps `η`,
infinitesimal along `l`, with `δ / η ≈ a`. If `M δ` and `E η` differ by `η` times an
infinitesimal, then `M (s a) = E s`. -/
lemma eq_of_infinitesimal_steps (M E : ℝ → A)
    (hM : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (hE : ContinuousOn E (Ici 0)) (hE0 : E 0 = 1)
    (hEadd : ∀ s t, 0 ≤ s → 0 ≤ t → E (s + t) = E s * E t)
    {ι : Type*} {l : Filter ι} [l.NeBot] (δ η : ι → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδη : ∀ n, δ n ≤ η n) (hη : ∀ n, 0 < η n) (hz : Tendsto η l (𝓝 0)) {a : ℝ}
    (ha : Tendsto (fun n => δ n / η n) l (𝓝 a))
    (hstep : Tendsto (fun n => (η n)⁻¹ • (M (δ n) - E (η n))) l (𝓝 0)) {s : ℝ} (hs : 0 ≤ s) :
    M (s * a) = E s := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hM.mono (Icc_subset_Ici_self : Icc 0 s ⊆ Ici 0))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hE.mono (Icc_subset_Ici_self : Icc 0 s ⊆ Ici 0))
  -- Take `N = ⌊s / η⌋` steps. The times: `N η ≈ s` and `N δ ≈ s a`.
  let N : ι → ℕ := fun n => ⌊s / η n⌋₊
  have hNs : ∀ n, (N n : ℝ) * η n ≤ s := fun n =>
    (le_div_iff₀ (hη n)).mp (Nat.floor_le (div_nonneg hs (hη n).le))
  have hNη : Tendsto (fun n => (N n : ℝ) * η n) l (𝓝 s) := by
    have hlo : ∀ n, s - η n ≤ (N n : ℝ) * η n := fun n => by
      have := Nat.lt_floor_add_one (s / η n)
      rw [div_lt_iff₀ (hη n), add_one_mul] at this
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hz) tendsto_const_nhds hlo hNs
  have hNδ : Tendsto (fun n => (N n : ℝ) * δ n) l (𝓝 (s * a)) :=
    (hNη.mul ha).congr fun n => by
      have := (hη n).ne'
      field_simp
  have ha0 : 0 ≤ a := ge_of_tendsto' ha fun n => div_nonneg (hδ n) (hη n).le
  have hMlim : Tendsto (fun n => M (N n * δ n)) l (𝓝 (M (s * a))) :=
    (hM _ (mul_nonneg hs ha0)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hNδ, Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (hδ n)⟩)
  have hElim : Tendsto (fun n => E (N n * η n)) l (𝓝 (E s)) :=
    (hE s hs).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hNη, Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (hη n).le⟩)
  -- Replacing the steps of `M` by those of `E` changes the result by `N η` times an
  -- infinitesimal.
  have hrepl : ∀ n, ‖M (N n * δ n) - E (N n * η n)‖ ≤
      N n * η n * (C * D * ‖(η n)⁻¹ • (M (δ n) - E (η n))‖) := fun n => by
    have h := norm_replace_steps_le M E h0 hadd hEadd hC hD (hδ n) (hη n).le (N n) le_rfl
      ((mul_le_mul_of_nonneg_left (hδη n) (Nat.cast_nonneg _)).trans (hNs n))
      (by simpa using hNs n)
    simp only [hE0, mul_one, add_zero] at h
    have := (hη n).ne'
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (hη n).le]
    refine h.trans_eq ?_
    field_simp
  have hzero : Tendsto (fun n => M (N n * δ n) - E (N n * η n)) l (𝓝 0) :=
    squeeze_zero_norm hrepl (by simpa using hNη.mul (hstep.norm.const_mul (C * D)))
  exact sub_eq_zero.mp (tendsto_nhds_unique (hMlim.sub hElim) hzero)

variable [CompleteSpace A]

/-- **Continuous semigroups are exponentials**, by Euler's infinitesimal argument. -/
theorem exists_eq_exp_of_semigroup_nonstandard [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  -- The positive infinitesimal `ε = 1 / ω`, as a sequence along `hyperfilter ℕ`, the scale
  -- `η`, and the change `q` on that scale.
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let η : ℕ → ℝ := fun n => ε n + ‖M (ε n) - 1‖
  let q : ℕ → A := fun n => (η n)⁻¹ • (M (ε n) - 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hεη : ∀ n, ε n ≤ η n := fun n => le_add_of_nonneg_right (norm_nonneg _)
  have hη : ∀ n, 0 < η n := fun n => (hε n).trans_le (hεη n)
  have hεz : Tendsto ε (hyperfilter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left Nat.hyperfilter_le_atTop
  have hηz : Tendsto η (hyperfilter ℕ) (𝓝 0) := by
    have hM : Tendsto (fun n => M (ε n)) (hyperfilter ℕ) (𝓝 1) := by
      simpa [h0, Function.comp_def] using (hcont 0 (by simp)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hεz, Eventually.of_forall fun n => (hε n).le⟩)
    simpa using hεz.add (hM.sub_const 1).norm
  have hsum : ∀ n, ε n / η n = 1 - ‖q n‖ := fun n => by
    have := (hη n).ne'
    simp only [q, norm_smul, norm_inv, Real.norm_of_nonneg (hη n).le]
    field_simp
    simp only [η]
    ring
  -- The standard part `B` of `q`, and `ε / η ≈ a = 1 - ‖B‖`.
  obtain ⟨B, hB1, hB : Tendsto q (hyperfilter ℕ) (𝓝 B)⟩ :=
    (isCompact_closedBall (0 : A) 1).ultrafilter_le_nhds (.map q (hyperfilter ℕ)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact mem_map.mpr (univ_mem' fun n => by
        simpa using (show ‖q n‖ ≤ 1 by
          linarith [hsum n, div_nonneg (hε n).le (hη n).le])))
  let a : ℝ := 1 - ‖B‖
  have ha : Tendsto (fun n => ε n / η n) (hyperfilter ℕ) (𝓝 a) :=
    (tendsto_const_nhds.sub hB.norm).congr fun n => (hsum n).symm
  -- The exponential `E u = exp (u B)` takes the same step on that scale, to first order.
  let E : ℝ → A := fun u => exp (u • B)
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun u =>
    (hasDerivAt_exp_smul_const B u).continuousAt
  have hEadd : ∀ u v, E (u + v) = E u * E v := fun u v => by
    simp only [E, add_smul]
    exact exp_add_of_commute (((Commute.refl B).smul_left u).smul_right v)
  have hEd : Tendsto (fun n => (η n)⁻¹ • (E (η n) - 1)) (hyperfilter ℕ) (𝓝 B) := by
    simpa [E, Function.comp_def] using
      (hasDerivAt_exp_smul_const' B 0).tendsto_slope_zero_right.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hηz, Eventually.of_forall hη⟩)
  have hstep : Tendsto (fun n => (η n)⁻¹ • (M (ε n) - E (η n))) (hyperfilter ℕ) (𝓝 0) := by
    simpa using (hB.sub hEd).congr fun n => by
      simp only [q, smul_sub]
      abel
  -- Euler's step, and the semigroup is not infinitely fast.
  have hmain : ∀ s, 0 ≤ s → M (s * a) = E s := fun s hs =>
    eq_of_infinitesimal_steps M E hcont h0 hadd hE.continuousOn (by simp [E])
      (fun u v _ _ => hEadd u v) ε η (fun n => (hε n).le) hεη hη hηz ha hstep hs
  have ha0 : a ≠ 0 := fun h => by
    have hB0 : B = 0 := tendsto_nhds_unique hEd (tendsto_const_nhds.congr fun n => by
      rw [← hmain _ (hη n).le, h, mul_zero, h0, sub_self, smul_zero])
    simp [a, hB0] at h
  have hapos : 0 < a :=
    lt_of_le_of_ne (sub_nonneg.mpr (mem_closedBall_zero_iff.mp hB1)) (Ne.symm ha0)
  refine ⟨a⁻¹ • B, fun t ht => ?_⟩
  have h := hmain (t / a) (div_nonneg ht hapos.le)
  rw [div_mul_cancel₀ t ha0] at h
  rw [h, smul_smul, div_eq_mul_inv]

end Experiments
