import Mathlib

/-!
# Bounded difference quotients of a continuous semigroup

Let `M` be a semigroup in a normed algebra, `M (s + t) = M s * M t` with `M 0 = 1`, continuous
at `0` from the right. If `‖M s - 1‖ ≤ 1/2` on `[0, δ]` and `h = δ / n`, then the average
`q = (1 + x + ⋯ + x ^ (n - 1)) / n` of the powers of `x = M h` is within `1/2` of `1`, and
`n (x - 1) q = x ^ n - 1 = M δ - 1`. Hence the difference quotients `(M h - 1) / h` along
`h = δ / (n + 1)` are bounded. Both proofs of the semigroup theorem in this folder start here.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace Experiments

lemma semigroup_nat_mul {E : Type*} [Monoid E] (M : ℝ → E) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    M ((n : ℝ) * h) = M h ^ n := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [Nat.cast_add_one, add_mul, one_mul,
      hadd _ _ (mul_nonneg (Nat.cast_nonneg n) hh) hh, ih, pow_succ]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

lemma geometric_average_near_one (x : A) {n : ℕ} (hn : 0 < n)
    (hx : ∀ k ∈ Finset.range n, ‖x ^ k - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1‖ ≤ (1 / 2 : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcount : (∑ _k ∈ Finset.range n, (1 : A)) = (n : ℝ) • (1 : A) := by
    simp [Algebra.smul_def]
  have havg :
      (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (x ^ k - 1)) =
        (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1 := by
    rw [Finset.sum_sub_distrib, hcount, smul_sub, smul_smul,
      inv_mul_cancel₀ hn', one_smul]
  rw [← havg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by exact_mod_cast hn))]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ‖x ^ k - 1‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _k ∈ Finset.range n, (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx) (by positivity)
    _ = _ := by simp [hn']

lemma geometric_quotient_bound (x : A) {n : ℕ} (hn : 0 < n)
    (hx : ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(n : ℝ) • (x - 1)‖ ≤ 2 * ‖x ^ n - 1‖ := by
  let d := (n : ℝ) • (x - 1)
  let q := (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have htel : d * q = x ^ n - 1 := by
    dsimp [d, q]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hn',
      one_smul, mul_geom_sum]
  have hq : ‖1 - q‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_sub_rev]
    exact hx
  have hbound : ‖d‖ ≤ ‖x ^ n - 1‖ + ‖d‖ * (1 / 2 : ℝ) := by
    calc
      ‖d‖ = ‖d * q + d * (1 - q)‖ := by congr 1; noncomm_ring
      _ ≤ ‖d * q‖ + ‖d * (1 - q)‖ := norm_add_le _ _
      _ ≤ ‖x ^ n - 1‖ + ‖d‖ * ‖1 - q‖ := by
        rw [htel]
        exact add_le_add (le_refl _) (norm_mul_le d (1 - q))
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hq (norm_nonneg d))
  change ‖d‖ ≤ _
  linarith

lemma semigroup_quotient_bound (M : ℝ → A) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    {δ : ℝ} (hδ : 0 < δ)
    (hnear : ∀ s ∈ Set.Icc 0 δ, ‖M s - 1‖ ≤ (1 / 2 : ℝ))
    {n : ℕ} (hn : 0 < n) :
    ‖(n : ℝ) • (M (δ / n) - 1)‖ ≤ 2 * ‖M δ - 1‖ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : 0 ≤ δ / (n : ℝ) := div_nonneg hδ.le (Nat.cast_nonneg n)
  have hnh : (n : ℝ) * (δ / n) = δ := mul_div_cancel₀ δ hn'
  have hp := semigroup_nat_mul M h0 hadd hh
  have hsteps : ∀ k ∈ Finset.range n, ‖M (δ / n) ^ k - 1‖ ≤ (1 / 2 : ℝ) := by
    intro k hk
    rw [← hp k]
    apply hnear
    refine ⟨mul_nonneg (Nat.cast_nonneg k) hh, ?_⟩
    calc
      _ ≤ (n : ℝ) * (δ / n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) hh
      _ = δ := hnh
  have hb := geometric_quotient_bound (M (δ / n)) hn
    (geometric_average_near_one (M (δ / n)) hn hsteps)
  simpa only [← hp n, hnh] using hb

/-- The difference quotients along `h = δ / (n + 1)` are bounded. -/
lemma exists_bounded_generators (M : ℝ → A)
    (hcont : ContinuousWithinAt M (Set.Ici 0) 0) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ δ > 0, ∃ C : ℝ, ∀ n : ℕ,
      ‖(δ / (n + 1 : ℝ))⁻¹ • (M (δ / (n + 1 : ℝ)) - 1)‖ ≤ C := by
  obtain ⟨r, hr, hclose⟩ :=
    Metric.continuousWithinAt_iff.mp hcont (1 / 2) (by norm_num)
  let δ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hnear : ∀ s ∈ Set.Icc 0 δ, ‖M s - 1‖ ≤ (1 / 2 : ℝ) := by
    intro s hs
    have hs' : dist s 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      dsimp [δ] at hs
      linarith [hs.2]
    simpa [dist_eq_norm, h0] using (hclose hs.1 hs').le
  refine ⟨δ, hδ, δ⁻¹ * (2 * ‖M δ - 1‖), ?_⟩
  intro n
  rw [inv_div, div_eq_inv_mul, mul_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hδ)]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  simpa only [Nat.cast_add_one] using
    semigroup_quotient_bound M h0 hadd hδ hnear (Nat.succ_pos n)

end Experiments
