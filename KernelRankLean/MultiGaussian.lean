import KernelRankLean.MultiComplexRank
import KernelRankLean.Sufficiency

/-!
# Exact `d`-way real rank of multi-Gaussian radial kernels

In `d ≥ 2` coordinates:

* **Alternating root-of-unity formula (`re_prod_eq_sum_re`).** For any `z₀, …, z_{d-1} ∈ ℂ`,
  `Re (∏ j, z j)` is a linear combination of `d` real products
  `∏ j, Re (z j · exp (-π i m / d))` (`m = 0, …, d - 1`). Thus a complex-rate Gaussian
  component in `d` dimensions needs only `d` real coordinatewise products (for instance, `3` in
  3-D rather than `2 ^ (3 - 1) = 4`), while a real-rate Gaussian needs `1`.
* **Finite `d`-way rank of all component sums.** Combining `isSumOfProducts_expPoly` with
  `re_prod_eq_sum_re` shows that every representation `cs` has finite `d`-way real separable rank.
* **Exact `d`-way real rank of multi-Gaussian representations.** When every component has
  `deg P = 0` (`r` real rates and `c` complex upper-half-plane rates), an Alder–Strassen
  substitution lower bound on `(ι_R → ℝ) × (ι_C → ℂ)` matches the upper bound `r + d · c`.
-/

open Complex Polynomial NNReal

namespace KernelRank

/-! ### `d`-term real product decomposition of `Re (∏ j, z j)` -/

/-- The real part of a `d`-fold complex product (`d ≥ 1`) is a weighted alternating sum of `d`
products of real parts rotated by `-π m / d`. -/
theorem re_prod_eq_sum_re {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℂ) :
    (∏ j, z j).re = (2 : ℝ) ^ (d - 1) / d *
      ∑ m : Fin d, (-1 : ℝ) ^ (m : ℕ) *
        ∏ j : Fin d, (z j * exp (-Real.pi * I * (m : ℕ) / d)).re := by
  have hd_pos : 0 < d := hd
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  apply Complex.ofReal_inj.mp
  push_cast
  have hre (w : ℂ) : (w.re : ℂ) = (starRingEnd ℂ w + w) / 2 := by
    rw [Complex.re_eq_add_conj]
    ring
  simp_rw [hre]
  have hconj_rot (j : Fin d) (m : ℕ) :
      starRingEnd ℂ (z j * exp (-Real.pi * I * m / d)) =
        starRingEnd ℂ (z j) * exp (Real.pi * I * m / d) := by
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp [div_eq_mul_inv]
  have hprod_div (m : Fin d) :
      (∏ j : Fin d,
        (starRingEnd ℂ (z j * exp (-Real.pi * I * (m : ℕ) / d)) +
          z j * exp (-Real.pi * I * (m : ℕ) / d)) / 2) =
      ((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ((∏ j ∈ S, starRingEnd ℂ (z j)) * ∏ j ∈ Finset.univ \ S, z j) *
            (exp (Real.pi * I * (m : ℕ) / d) ^ S.card *
              exp (-Real.pi * I * (m : ℕ) / d) ^ (d - S.card)) := by
    simp_rw [hconj_rot, div_eq_mul_inv]
    rw [Finset.prod_mul_distrib]
    have h2 : (∏ _j : Fin d, (2 : ℂ)⁻¹) = ((2 : ℂ) ^ d)⁻¹ := by simp
    rw [h2, mul_comm _ (((2 : ℂ) ^ d)⁻¹)]
    congr 1
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hsub : S ⊆ Finset.univ := Finset.mem_powerset.mp hS
    have hcard : (Finset.univ \ S).card = d - S.card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      hcard]
    ring
  simp_rw [hprod_div]
  let Z (S : Finset (Fin d)) : ℂ :=
    (∏ j ∈ S, starRingEnd ℂ (z j)) * ∏ j ∈ Finset.univ \ S, z j
  change _ = (2 : ℂ) ^ (d - 1) / d *
    ∑ m : Fin d, (-1 : ℂ) ^ (m : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
        (exp (Real.pi * I * (m : ℕ) / d) ^ S.card *
          exp (-Real.pi * I * (m : ℕ) / d) ^ (d - S.card)))
  have hpull : ∑ m : Fin d,
      (-1 : ℂ) ^ (m : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
          (exp (Real.pi * I * (m : ℕ) / d) ^ S.card *
            exp (-Real.pi * I * (m : ℕ) / d) ^ (d - S.card))) =
      ((2 : ℂ) ^ d)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
        ∑ m ∈ Finset.range d,
          (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
            exp (-Real.pi * I * m / d) ^ (d - S.card)) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun m : ℕ => (-1 : ℂ) ^ m * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
          (exp (Real.pi * I * m / d) ^ S.card *
            exp (-Real.pi * I * m / d) ^ (d - S.card)))) d]
    simp_rw [← mul_assoc ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹),
      mul_comm ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹), mul_assoc (((2 : ℂ) ^ d)⁻¹), ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun m _ => by ring
  rw [hpull]
  have hinner (S : Finset (Fin d)) (hS : S ∈ (Finset.univ : Finset (Fin d)).powerset) :
      (∑ m ∈ Finset.range d,
        (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
          exp (-Real.pi * I * m / d) ^ (d - S.card))) =
        if S = ∅ ∨ S = Finset.univ then (d : ℂ) else 0 := by
    have hcard_le : S.card ≤ d := by
      simpa using Finset.card_le_univ S
    let w : ℂ := exp (2 * Real.pi * I * S.card / d)
    have hterm (m : ℕ) :
        (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
          exp (-Real.pi * I * m / d) ^ (d - S.card)) = w ^ m := by
      have hm1 : (-1 : ℂ) ^ m = exp (Real.pi * I * m) := by
        rw [mul_comm (Real.pi * I) (m : ℂ), exp_nat_mul, exp_pi_mul_I]
      rw [hm1, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add, ← exp_nat_mul]
      congr 1
      have hsub_cast : ((d - S.card : ℕ) : ℂ) = (d : ℂ) - (S.card : ℂ) :=
        Nat.cast_sub hcard_le
      rw [hsub_cast]
      field_simp
      ring
    simp_rw [hterm]
    split_ifs with hSu
    · rcases hSu with rfl | rfl
      · simp [w]
      · have hw1 : w = 1 := by
          simp only [w, Finset.card_univ, Fintype.card_fin]
          have : 2 * Real.pi * I * (d : ℂ) / (d : ℂ) = 2 * Real.pi * I := by field_simp
          rw [this, exp_two_pi_mul_I]
        simp [hw1]
    · push Not at hSu
      have hpos_S : 0 < S.card := Finset.card_pos.mpr hSu.1
      have hlt_S : S.card < d := by
        have hssub : S ⊂ Finset.univ := (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ S, hSu.2⟩)
        simpa using Finset.card_lt_card hssub
      have hwd : w ^ d = 1 := by
        rw [← exp_nat_mul]
        have hexp : (d : ℂ) * (2 * Real.pi * I * S.card / d) =
            (S.card : ℂ) * (2 * Real.pi * I) := by field_simp
        rw [hexp, exp_nat_mul_two_pi_mul_I]
      have hw1 : w ≠ 1 := by
        intro h1
        rw [exp_eq_one_iff] at h1
        obtain ⟨m, hm⟩ := h1
        have hpi : (2 : ℂ) * Real.pi * I ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            I_ne_zero
        have heq : (S.card : ℂ) = (m : ℂ) * d := by
          apply mul_right_cancel₀ hpi
          have hm' : 2 * Real.pi * I * (S.card : ℂ) = (m : ℂ) * (2 * Real.pi * I) * d :=
            (div_eq_iff hd0).mp hm
          linear_combination hm'
        have hz : (S.card : ℤ) = m * d := by exact_mod_cast heq
        rcases le_or_gt m 0 with hm_le | hm_pos
        · have : m * (d : ℤ) ≤ 0 :=
            Int.mul_nonpos_of_nonpos_of_nonneg hm_le (Int.natCast_nonneg d)
          omega
        · have hm1 : 1 ≤ m := by omega
          have : 1 * (d : ℤ) ≤ m * (d : ℤ) :=
            Int.mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg d)
          omega
      have hgeom := geom_sum_mul w d
      rw [hwd, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw1)
  have hsumZ : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Z S *
      (∑ m ∈ Finset.range d,
        (-1 : ℂ) ^ m * (exp (Real.pi * I * m / d) ^ S.card *
          exp (-Real.pi * I * m / d) ^ (d - S.card))) =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        Z S * if S = ∅ ∨ S = Finset.univ then (d : ℂ) else 0 :=
    Finset.sum_congr rfl fun S hS => by rw [hinner S hS]
  rw [hsumZ]
  simp only [mul_ite, mul_zero, ← Finset.sum_filter]
  have hfilt : (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => S = ∅ ∨ S = Finset.univ) = {∅, Finset.univ} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
  have hne_univ : (∅ : Finset (Fin d)) ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  rw [hfilt, Finset.sum_pair hne_univ]
  have hpow2 : (2 : ℂ) ^ d = (2 : ℂ) ^ (d - 1) * 2 := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  have h2ne : (2 : ℂ) ^ (d - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [Z, Finset.prod_empty, Finset.sdiff_empty, Finset.sdiff_self, map_one, mul_one,
    ← map_prod (starRingEnd ℂ), hpow2]
  field_simp
  ring

/-- Taking the real part of an `N`-term complex `d`-way product sum (`d ≥ 1`) gives an
`(N * d)`-term real `d`-way product sum. -/
lemma IsSumOfProducts.re {d N : ℕ} (hd : 1 ≤ d) {X : Fin d → Type*}
    {K : (∀ j, X j) → ℂ} (hK : IsSumOfProducts K N) :
    IsSumOfProducts (fun x => (K x).re) (N * d) := by
  obtain ⟨f, hf⟩ := hK
  have hsingle (n : Fin N) :
      IsSumOfProducts (fun x : ∀ j, X j => (∏ j, f n j (x j)).re) d := by
    let j₀ : Fin d := ⟨0, hd⟩
    refine ⟨fun m j u =>
      if j = j₀ then
        (2 : ℝ) ^ (d - 1) / d * (-1 : ℝ) ^ (m : ℕ) *
          (f n j u * exp (-Real.pi * I * (m : ℕ) / d)).re
      else
        (f n j u * exp (-Real.pi * I * (m : ℕ) / d)).re, fun x => ?_⟩
    dsimp only
    rw [re_prod_eq_sum_re hd (fun j => f n j (x j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re) (Finset.mem_univ j₀)]
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have her : ∏ j ∈ Finset.univ.erase j₀,
        (if j = j₀ then
          (2 : ℝ) ^ (d - 1) / d * (-1 : ℝ) ^ (m : ℕ) *
            (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re
        else
          (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re) =
        ∏ j ∈ Finset.univ.erase j₀,
          (f n j (x j) * exp (-Real.pi * I * (m : ℕ) / d)).re :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    rw [her]
    simp only [↓reduceIte]
    ring
  have hsum := IsSumOfProducts.finsetSum hsingle
  have hcard : (∑ _n : Fin N, d) = N * d := by simp
  rw [hcard] at hsum
  have heq : (fun x : ∀ j, X j => (K x).re) = fun x => ∑ n : Fin N, (∏ j, f n j (x j)).re := by
    funext x
    rw [hf x, Complex.re_sum]
  rwa [← heq] at hsum

/-- Every exponential-polynomial component has finite `d`-way real separable rank (`d ≥ 2`). -/
lemma isSumOfProducts_radial_component {d : ℕ} (hd : 2 ≤ d) (c : Component) :
    IsSumOfProducts (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2))
      (((d - 1) * c.poly.natDegree + 1) * d) := by
  have hcpx : IsSumOfProducts
      (fun x : Fin d → ℝ => expPoly c.poly c.rate (∑ j, x j ^ 2))
      ((d - 1) * c.poly.natDegree + 1) :=
    (isSumOfProducts_expPoly hd c.poly c.rate).comp
      (fun _ x => (⟨x ^ 2, sq_nonneg x⟩ : ℝ≥0))
  exact hcpx.re (by omega)

/-- Every list of components gives a `d`-D radial kernel of finite separable rank (`d ≥ 2`). -/
theorem separableRank_radial_profile_lt_top {d : ℕ} (hd : 2 ≤ d) (cs : List Component) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) < ⊤ := by
  let comp (i : Fin cs.length) : Component := cs[i]
  have hprof : (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      fun x => ∑ i : Fin cs.length, (comp i).eval (∑ j, x j ^ 2) := by
    funext x
    exact (Fin.sum_univ_fun_getElem cs fun c => c.eval (∑ j, x j ^ 2)).symm
  rw [hprof]
  exact lt_of_le_of_lt
    (iInf₂_le _ (IsSumOfProducts.finsetSum fun i => isSumOfProducts_radial_component hd (comp i)))
    (WithTop.coe_lt_top _)

/-- A well-formed Gaussian component (`deg P = 0`) is a sum of `c.gaussianCost d` real `d`-way
products (`1` if its rate is real, `d` if complex), for any `d ≥ 1`. -/
lemma isSumOfProducts_radial_gaussianComponent {d : ℕ} (hd : 1 ≤ d) {c : Component}
    (hwf : c.WellFormed) (hg : c.IsGaussian) :
    IsSumOfProducts (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2)) (c.gaussianCost d) := by
  have hp : c.poly = C (c.poly.coeff 0) := eq_C_of_natDegree_eq_zero hg
  let j₀ : Fin d := ⟨0, hd⟩
  by_cases him : c.rate.im = 0
  · have hcoeff_im : (c.poly.coeff 0).im = 0 := hwf.2.2 him 0
    have hrate : c.rate = (c.rate.re : ℂ) := Complex.ext rfl (by simpa using him)
    have hcoeff : c.poly.coeff 0 = ((c.poly.coeff 0).re : ℂ) :=
      Complex.ext rfl (by simpa using hcoeff_im)
    simp only [Component.gaussianCost, him, ↓reduceIte]
    refine ⟨fun _ j u =>
      if j = j₀ then (c.poly.coeff 0).re * Real.exp (c.rate.re * u ^ 2)
      else Real.exp (c.rate.re * u ^ 2), fun x => ?_⟩
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have heval : c.eval (∑ j, x j ^ 2) =
        (c.poly.coeff 0).re * Real.exp (c.rate.re * ∑ j, x j ^ 2) := by
      simp only [Component.eval]
      conv_lhs => rw [hp]
      rw [eval_C, hcoeff, hrate, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      simp only [Complex.ofReal_re]
    rw [heval, Finset.mul_sum, Real.exp_sum]
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ (fun j => Real.exp (c.rate.re * x j ^ 2))
        (Finset.mem_univ j₀)]
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have her : ∏ j ∈ Finset.univ.erase j₀,
        (if j = j₀ then (c.poly.coeff 0).re * Real.exp (c.rate.re * x j ^ 2)
         else Real.exp (c.rate.re * x j ^ 2)) =
        ∏ j ∈ Finset.univ.erase j₀, Real.exp (c.rate.re * x j ^ 2) :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    rw [her]
    simp only [↓reduceIte, mul_assoc]
  · simp only [Component.gaussianCost, him, ↓reduceIte]
    have hcpx : IsSumOfProducts
        (fun x : Fin d → ℝ => c.poly.coeff 0 * exp (c.rate * (∑ j, x j ^ 2 : ℝ))) 1 := by
      refine ⟨fun _ j u =>
        if j = j₀ then c.poly.coeff 0 * exp (c.rate * (u ^ 2 : ℝ))
        else exp (c.rate * (u ^ 2 : ℝ)), fun x => ?_⟩
      dsimp only
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
        Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      conv_lhs =>
        rw [← Finset.mul_prod_erase Finset.univ (fun j => exp (c.rate * (x j ^ 2 : ℝ)))
          (Finset.mem_univ j₀)]
      conv_rhs =>
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
      have her : ∏ j ∈ Finset.univ.erase j₀,
          (if j = j₀ then c.poly.coeff 0 * exp (c.rate * (x j ^ 2 : ℝ))
           else exp (c.rate * (x j ^ 2 : ℝ))) =
          ∏ j ∈ Finset.univ.erase j₀, exp (c.rate * (x j ^ 2 : ℝ)) :=
        Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
      rw [her]
      simp only [↓reduceIte, mul_assoc]
    have hre := hcpx.re hd
    rw [one_mul] at hre
    have heq : (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2)) =
        fun x => (c.poly.coeff 0 * exp (c.rate * (∑ j, x j ^ 2 : ℝ))).re := by
      funext x
      simp only [Component.eval]
      conv_lhs => rw [hp]
      rw [eval_C]
    rwa [← heq] at hre

/-! ### Alder–Strassen substitution lower bound on `(ι_R → ℝ) × (ι_C → ℂ)` -/

/-- Every `ℝ`-linear functional `ℂ →ₗ[ℝ] ℝ` has a nonzero vector in its kernel. -/
lemma exists_ker_ne_zero (L : ℂ →ₗ[ℝ] ℝ) : ∃ w : ℂ, w ≠ 0 ∧ L w = 0 := by
  by_cases h0 : L 1 = 0 ∧ L I = 0
  · exact ⟨1, one_ne_zero, h0.1⟩
  · refine ⟨(L I : ℂ) - (L 1 : ℂ) * I, ?_, ?_⟩
    · intro h
      have hre : L I = 0 := by simpa using congrArg Complex.re h
      have him : -L 1 = 0 := by simpa using congrArg Complex.im h
      exact h0 ⟨neg_eq_zero.mp him, hre⟩
    · have hw : ((L I : ℂ) - (L 1 : ℂ) * I) = (L I) • (1 : ℂ) - (L 1) • I := by
        simp [Complex.real_smul]
      rw [hw, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring

/-- A single nonzero `d`-fold complex product `Re (β ∏ j, z j)` (`d ≥ 2`) has real rank at
least `d`. -/
lemma single_complex_rank_ge {d : ℕ} (hd : 2 ≤ d) :
    ∀ {β : ℂ}, β ≠ 0 → ∀ {R : ℕ} (ℓ : Fin R → Fin d → (ℂ →ₗ[ℝ] ℝ)),
      (∀ z : Fin d → ℂ, (β * ∏ j, z j).re = ∑ n, ∏ j, ℓ n j (z j)) → d ≤ R := by
  induction d, hd using Nat.le_induction with
  | base =>
    intro β hβ R ℓ hrepr
    by_contra hlt
    rcases (show R = 0 ∨ R = 1 by omega) with rfl | rfl
    · have h := hrepr (fin2Vec 1 (starRingEnd ℂ β))
      simp only [Fin.prod_univ_two, fin2Vec_zero, fin2Vec_one, one_mul, Finset.univ_eq_empty,
        Finset.sum_empty] at h
      rw [Complex.mul_conj, Complex.ofReal_re] at h
      exact (Complex.normSq_pos.mpr hβ).ne' h
    · obtain ⟨w, hw0, hw_ker⟩ := exists_ker_ne_zero (ℓ 0 0)
      have h := hrepr (fin2Vec w (starRingEnd ℂ (β * w)))
      simp only [Fin.prod_univ_two, fin2Vec_zero, fin2Vec_one, Finset.univ_unique,
        Fin.default_eq_zero, Finset.sum_singleton, hw_ker, zero_mul] at h
      rw [← mul_assoc, Complex.mul_conj, Complex.ofReal_re] at h
      exact (Complex.normSq_pos.mpr (mul_ne_zero hβ hw0)).ne' h
  | succ d hd ih =>
    intro β hβ R ℓ hrepr
    cases R with
    | zero =>
      exfalso
      let z (j : Fin (d + 1)) : ℂ := if j = 0 then starRingEnd ℂ β else 1
      have hprod : ∏ j : Fin (d + 1), z j = starRingEnd ℂ β := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (d + 1)))]
        have her : ∏ j ∈ Finset.univ.erase (0 : Fin (d + 1)), z j = 1 :=
          Finset.prod_eq_one fun j hj => by simp [z, Finset.ne_of_mem_erase hj]
        simp [z, her]
      have h := hrepr z
      simp only [hprod, Finset.univ_eq_empty, Finset.sum_empty, Complex.mul_conj,
        Complex.ofReal_re] at h
      exact (Complex.normSq_pos.mpr hβ).ne' h
    | succ R =>
      obtain ⟨w, hw0, hw_ker⟩ := exists_ker_ne_zero (ℓ (Fin.last R) (Fin.last d))
      have hd0 : 0 < d := by omega
      let j₀ : Fin d := ⟨0, hd0⟩
      let ℓ' (n : Fin R) (j : Fin d) : ℂ →ₗ[ℝ] ℝ :=
        if j = j₀ then (ℓ n.castSucc (Fin.last d) w) • ℓ n.castSucc j.castSucc
        else ℓ n.castSucc j.castSucc
      have hrepr' (z : Fin d → ℂ) :
          ((β * w) * ∏ j, z j).re = ∑ n : Fin R, ∏ j, ℓ' n j (z j) := by
        have h := hrepr (Fin.snoc (α := fun _ => ℂ) z w)
        rw [Fin.prod_univ_castSucc] at h
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
        have hbw : β * ((∏ j, z j) * w) = (β * w) * ∏ j, z j := by ring
        rw [hbw, Fin.sum_univ_castSucc] at h
        have hlast : (∏ j : Fin (d + 1),
            ℓ (Fin.last R) j (Fin.snoc (α := fun _ => ℂ) z w j)) = 0 := by
          rw [Fin.prod_univ_castSucc, Fin.snoc_last, hw_ker, mul_zero]
        rw [hlast, add_zero] at h
        rw [h]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← Finset.mul_prod_erase Finset.univ (fun j => ℓ' n j (z j)) (Finset.mem_univ j₀),
          ← Finset.mul_prod_erase Finset.univ (fun j => ℓ n.castSucc j.castSucc (z j))
            (Finset.mem_univ j₀)]
        have her : ∏ j ∈ Finset.univ.erase j₀, ℓ' n j (z j) =
            ∏ j ∈ Finset.univ.erase j₀, ℓ n.castSucc j.castSucc (z j) :=
          Finset.prod_congr rfl fun j hj => by
            simp [ℓ', Finset.ne_of_mem_erase hj]
        rw [her]
        have hj₀ : ℓ' n j₀ (z j₀) =
            ℓ n.castSucc (Fin.last d) w * ℓ n.castSucc j₀.castSucc (z j₀) := by
          simp [ℓ']
        rw [hj₀]
        ring
      have hle := ih (mul_ne_zero hβ hw0) ℓ' hrepr'
      omega

/-- Space `(ι_R → ℝ) × (ι_C → ℂ)` for real and complex Gaussian rates. -/
abbrev GaussianSpace (ι_R ι_C : Type*) : Type _ :=
  (ι_R → ℝ) × (ι_C → ℂ)

/-- Real `d`-multilinear form of `S_R` real rates and `S_C` complex rates. -/
noncomputable def gaussianForm {ι_R ι_C : Type*} (d : ℕ) (S_R : Finset ι_R) (S_C : Finset ι_C)
    (α : ι_R → ℝ) (β : ι_C → ℂ) (u : Fin d → GaussianSpace ι_R ι_C) : ℝ :=
  (∑ i ∈ S_R, α i * ∏ j : Fin d, (u j).1 i) +
    ∑ k ∈ S_C, (β k * ∏ j : Fin d, (u j).2 k).re

/-- Peeling lower bound for purely real Gaussian blocks (`S_C = ∅`). -/
lemma gaussianForm_real_rank_ge {ι_R ι_C : Type*} {d : ℕ} (hd : 2 ≤ d)
    (S_R : Finset ι_R) (α : ι_R → ℝ) (hα : ∀ i ∈ S_R, α i ≠ 0) :
    ∀ {R : ℕ} (ℓ : Fin R → Fin d → (GaussianSpace ι_R ι_C →ₗ[ℝ] ℝ)),
      (∀ u, gaussianForm d S_R ∅ α (fun _ => 0) u = ∑ n, ∏ j, ℓ n j (u j)) →
      S_R.card ≤ R := by
  let := Classical.decEq ι_R
  induction S_R using Finset.induction_on with
  | empty => intros; simp
  | insert i₀ S_R hi₀ ih =>
    intro R ℓ hrepr
    have hd0 : 0 < d := by omega
    let j₀ : Fin d := ⟨0, hd0⟩
    let j₁ : Fin d := ⟨1, hd⟩
    have hj₁ : j₁ ≠ j₀ := by simp [j₁, j₀, Fin.ext_iff]
    let e₀ : GaussianSpace ι_R ι_C := (Pi.single i₀ 1, 0)
    have hTe : gaussianForm d (insert i₀ S_R) ∅ α (fun _ => 0) (fun _ => e₀) = α i₀ := by
      simp only [gaussianForm, Finset.sum_empty, add_zero]
      rw [Finset.sum_insert hi₀]
      have hrest : ∑ i ∈ S_R, α i * ∏ _j : Fin d, e₀.1 i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          have hne : i ≠ i₀ := fun h => hi₀ (h ▸ hi)
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [e₀, hne]), mul_zero]
      rw [hrest, add_zero]
      simp [e₀]
    have hα0 : α i₀ ≠ 0 := hα i₀ (Finset.mem_insert_self i₀ S_R)
    obtain ⟨n₀, _, hn₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by rw [← hrepr]; exact hTe ▸ hα0)
    have hℓ0 : ℓ n₀ j₀ e₀ ≠ 0 := fun h =>
      hn₀ (Finset.prod_eq_zero (Finset.mem_univ j₀) h)
    let killR : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      { toFun := fun x => (Function.update x.1 i₀ 0, x.2)
        map_add' := fun a b => by
          ext i <;> simp only [Prod.fst_add, Prod.snd_add]
          · by_cases h : i = i₀ <;> simp [h]
        map_smul' := fun a b => by
          ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
          · by_cases h : i = i₀ <;> simp [h] }
    let φ₀ : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      killR - ((ℓ n₀ j₀ e₀)⁻¹ • (ℓ n₀ j₀).comp killR).smulRight e₀
    have hφ₀_kill (x : GaussianSpace ι_R ι_C) : ℓ n₀ j₀ (φ₀ x) = 0 := by
      simp only [φ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    let φ (j : Fin d) : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      if j = j₀ then φ₀ else killR
    let rem : Finset (Fin R) := Finset.univ.erase n₀
    have hRpos : 1 ≤ R := Fin.pos n₀
    let eRem : Fin (R - 1) ≃ rem := (Fintype.equivFinOfCardEq (by simp [rem])).symm
    let ℓ' (m : Fin (R - 1)) (j : Fin d) : GaussianSpace ι_R ι_C →ₗ[ℝ] ℝ :=
      (ℓ (eRem m).1 j).comp (φ j)
    have hrepr' (u : Fin d → GaussianSpace ι_R ι_C) :
        gaussianForm d S_R ∅ α (fun _ => 0) u = ∑ m : Fin (R - 1), ∏ j, ℓ' m j (u j) := by
      have hT : gaussianForm d S_R ∅ α (fun _ => 0) u =
          gaussianForm d (insert i₀ S_R) ∅ α (fun _ => 0) (fun j => φ j (u j)) := by
        simp only [gaussianForm, Finset.sum_empty, add_zero, Finset.sum_insert hi₀]
        have hz : α i₀ * (∏ j : Fin d, (φ j (u j)).1 i₀) = 0 := by
          rw [Finset.prod_eq_zero (Finset.mem_univ j₁) (by simp [φ, hj₁, killR]), mul_zero]
        rw [hz, zero_add]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i₀ := fun h => hi₀ (h ▸ hi)
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = j₀ <;> simp [φ, hj, φ₀, killR, hne, e₀]
      rw [hT, hrepr, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ n₀)]
      have hdead : (∏ j : Fin d, ℓ n₀ j (φ j (u j))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [φ, hφ₀_kill])
      rw [hdead, zero_add]
      change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
      rw [← Finset.sum_coe_sort rem]
      exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
    have hle := ih (fun i hi => hα i (Finset.mem_insert_of_mem hi)) ℓ' hrepr'
    rw [Finset.card_insert_of_notMem hi₀]
    omega

/-- Alder–Strassen peeling lower bound `S_R.card + d * S_C.card ≤ R` for `gaussianForm`. -/
lemma gaussianForm_rank_ge {ι_R ι_C : Type*} {d : ℕ} (hd : 2 ≤ d)
    (S_R : Finset ι_R) (S_C : Finset ι_C) (α : ι_R → ℝ) (β : ι_C → ℂ)
    (hα : ∀ i ∈ S_R, α i ≠ 0) (hβ : ∀ k ∈ S_C, β k ≠ 0) :
    ∀ {R : ℕ} (ℓ : Fin R → Fin d → (GaussianSpace ι_R ι_C →ₗ[ℝ] ℝ)),
      (∀ u, gaussianForm d S_R S_C α β u = ∑ n, ∏ j, ℓ n j (u j)) →
      S_R.card + d * S_C.card ≤ R := by
  let := Classical.decEq ι_C
  induction S_C using Finset.induction_on with
  | empty =>
    intro R ℓ hrepr
    simp only [Finset.card_empty, mul_zero, add_zero]
    refine gaussianForm_real_rank_ge hd S_R α hα ℓ fun u => ?_
    simpa [gaussianForm] using hrepr u
  | insert k₀ S_C hk₀ ih =>
    intro R ℓ hrepr
    have hd0 : 0 < d := by omega
    let j₀ : Fin d := ⟨0, hd0⟩
    let j₁ : Fin d := ⟨1, hd⟩
    have hj₁ : j₁ ≠ j₀ := by simp [j₁, j₀, Fin.ext_iff]
    let jLast : Fin d := ⟨d - 1, by omega⟩
    let embC : ℂ →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      { toFun := fun z => (0, Pi.single k₀ z)
        map_add' := fun a b => by ext i <;> simp [Pi.single_add]
        map_smul' := fun a b => by
          ext i
          · simp
          · by_cases h : i = k₀ <;> simp [h, Complex.real_smul] }
    let killC : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      { toFun := fun x => (x.1, Function.update x.2 k₀ 0)
        map_add' := fun a b => by
          ext i <;> simp only [Prod.fst_add, Prod.snd_add]
          · by_cases h : i = k₀ <;> simp [h]
        map_smul' := fun a b => by
          ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
          · by_cases h : i = k₀ <;> simp [h] }
    have hT_emb (z : Fin d → ℂ) :
        gaussianForm d S_R (insert k₀ S_C) α β (fun j => embC (z j)) =
          (β k₀ * ∏ j, z j).re := by
      simp only [gaussianForm, Finset.sum_insert hk₀]
      have hR0 : (∑ i ∈ S_R, α i * ∏ j : Fin d, (embC (z j)).1 i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [embC]), mul_zero]
      have hC0 : (∑ k ∈ S_C, (β k * ∏ j : Fin d, (embC (z j)).2 k).re) = 0 :=
        Finset.sum_eq_zero fun k hk => by
          have hne : k ≠ k₀ := fun h => hk₀ (h ▸ hk)
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [embC, hne]),
            mul_zero, zero_re]
      rw [hR0, zero_add, hC0, add_zero]
      simp [embC]
    have hβ0 : β k₀ ≠ 0 := hβ k₀ (Finset.mem_insert_self k₀ S_C)
    -- Step 1: peel `2` terms in mode `0` via triangular elimination on `ℂ ≅ ℝ²`.
    have hex1 : ∃ n₁ : Fin R, ℓ n₁ j₀ (embC 1) ≠ 0 := by
      let z (j : Fin d) : ℂ := if j = j₁ then starRingEnd ℂ (β k₀) else 1
      have hzprod : ∏ j : Fin d, z j = starRingEnd ℂ (β k₀) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₁)]
        have her : ∏ j ∈ Finset.univ.erase j₁, z j = 1 :=
          Finset.prod_eq_one fun j hj => by simp [z, Finset.ne_of_mem_erase hj]
        simp [z, her]
      have hne : ∑ n : Fin R, ∏ j, ℓ n j (embC (z j)) ≠ 0 := by
        rw [← hrepr, hT_emb, hzprod, Complex.mul_conj, Complex.ofReal_re]
        exact (Complex.normSq_pos.mpr hβ0).ne'
      obtain ⟨n₁, _, hn₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      refine ⟨n₁, fun h => hn₁ (Finset.prod_eq_zero (Finset.mem_univ j₀) ?_)⟩
      simpa [z, hj₁.symm] using h
    obtain ⟨n₁, hn₁⟩ := hex1
    obtain ⟨w₁, hw₁0, hw₁_ker⟩ := exists_ker_ne_zero ((ℓ n₁ j₀).comp embC)
    have hex2 : ∃ n₂ : Fin R, n₂ ≠ n₁ ∧ ℓ n₂ j₀ (embC w₁) ≠ 0 := by
      let z (j : Fin d) : ℂ :=
        if j = j₀ then w₁ else if j = j₁ then starRingEnd ℂ (β k₀ * w₁) else 1
      have hzprod : ∏ j : Fin d, z j = w₁ * starRingEnd ℂ (β k₀ * w₁) := by
        have hsub : ({j₀, j₁} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
        rw [← Finset.prod_sdiff hsub, Finset.prod_pair hj₁.symm]
        have her : ∏ j ∈ Finset.univ \ {j₀, j₁}, z j = 1 :=
          Finset.prod_eq_one fun j hj => by
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hj
            push Not at hj
            simp [z, hj.2.1, hj.2.2]
        rw [her, one_mul]
        simp [z, hj₁]
      have hne : ∑ n : Fin R, ∏ j, ℓ n j (embC (z j)) ≠ 0 := by
        rw [← hrepr, hT_emb, hzprod, ← mul_assoc, Complex.mul_conj, Complex.ofReal_re]
        exact (Complex.normSq_pos.mpr (mul_ne_zero hβ0 hw₁0)).ne'
      obtain ⟨n₂, _, hn₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hℓ2 : ℓ n₂ j₀ (embC w₁) ≠ 0 := fun h =>
        hn₂ (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simpa [z] using h))
      exact ⟨n₂, fun h => hℓ2 (h ▸ hw₁_ker), hℓ2⟩
    obtain ⟨n₂, hn₂₁, hn₂⟩ := hex2
    let ψ₀a : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      killC - ((ℓ n₁ j₀ (embC 1))⁻¹ • (ℓ n₁ j₀).comp killC).smulRight (embC 1)
    let ψ₀ : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      ψ₀a - ((ℓ n₂ j₀ (embC w₁))⁻¹ • (ℓ n₂ j₀).comp ψ₀a).smulRight (embC w₁)
    have hψ₀_kill1 (x : GaussianSpace ι_R ι_C) : ℓ n₁ j₀ (ψ₀ x) = 0 := by
      have ha : ℓ n₁ j₀ (ψ₀a x) = 0 := by
        simp only [ψ₀a, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
        field_simp
        ring
      have hb : ℓ n₁ j₀ (embC w₁) = 0 := hw₁_ker
      simp only [ψ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, map_sub, map_smul,
        ha, hb, smul_zero, sub_zero]
    have hψ₀_kill2 (x : GaussianSpace ι_R ι_C) : ℓ n₂ j₀ (ψ₀ x) = 0 := by
      simp only [ψ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    -- Step 2: peel `1` more term in each mode `1, …, d - 2`, reaching `d` dead terms in total.
    have hpeel : ∀ m ≤ d - 2,
        ∃ (D : Finset (Fin R))
          (ψ : Fin d → (GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C)),
        D.card = m + 2 ∧
        (∀ j : Fin d, (j : ℕ) < m + 1 →
          ∃ c_j : GaussianSpace ι_R ι_C →ₗ[ℝ] ℂ, ∀ x, ψ j x = killC x - embC (c_j x)) ∧
        (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < m + 1 ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
      intro m hm
      induction m with
      | zero =>
        refine ⟨{n₁, n₂}, fun _ => ψ₀, Finset.card_pair hn₂₁.symm, ?_, ?_⟩
        · intro j hj
          have hj0 : j = j₀ := by ext; simp [j₀]; omega
          subst hj0
          let c₁ : GaussianSpace ι_R ι_C →ₗ[ℝ] ℂ :=
            ((ℓ n₁ j₀ (embC 1))⁻¹ • (ℓ n₁ j₀).comp killC).smulRight (1 : ℂ)
          let c₂ : GaussianSpace ι_R ι_C →ₗ[ℝ] ℂ :=
            ((ℓ n₂ j₀ (embC w₁))⁻¹ • (ℓ n₂ j₀).comp ψ₀a).smulRight w₁
          refine ⟨c₁ + c₂, fun x => ?_⟩
          simp only [ψ₀, ψ₀a, c₁, c₂, LinearMap.add_apply, LinearMap.sub_apply,
            LinearMap.smulRight_apply, map_add, map_smul]
          abel
        · intro n hn
          rcases Finset.mem_insert.mp hn with rfl | hn'
          · exact ⟨j₀, by simp [j₀], hψ₀_kill1⟩
          · rw [Finset.mem_singleton.mp hn']
            exact ⟨j₀, by simp [j₀], hψ₀_kill2⟩
      | succ m ihm =>
        obtain ⟨D, ψ, hDcard, hψ_form, hDkill⟩ := ihm (by omega)
        let jm : Fin d := ⟨m + 1, by omega⟩
        have hex_next : ∃ nr ∉ D, ∃ wr : ℂ, ℓ nr jm (embC wr) ≠ 0 := by
          by_contra hall
          push Not at hall
          let eD : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
          let ℓD (p : Fin D.card) (j : Fin d) : ℂ →ₗ[ℝ] ℝ := (ℓ (eD p).1 j).comp embC
          have hD_repr (z : Fin d → ℂ) :
              (β k₀ * ∏ j, z j).re = ∑ p : Fin D.card, ∏ j, ℓD p j (z j) := by
            rw [← hT_emb, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
            have hsdiff : ∑ n ∈ Finset.univ \ D, ∏ j, ℓ n j (embC (z j)) = 0 :=
              Finset.sum_eq_zero fun n hn =>
                Finset.prod_eq_zero (Finset.mem_univ jm) (hall n (Finset.mem_sdiff.mp hn).2 (z jm))
            rw [hsdiff, zero_add]
            change ∑ n ∈ D, ∏ j, ℓ n j (embC (z j)) = _
            rw [← Finset.sum_coe_sort D]
            exact (eD.sum_comp (fun x : D => ∏ j, ℓ x.1 j (embC (z j)))).symm
          have hge := single_complex_rank_ge hd hβ0 ℓD hD_repr
          omega
        obtain ⟨nr, hnr_notD, wr, hwr⟩ := hex_next
        let cr : GaussianSpace ι_R ι_C →ₗ[ℝ] ℂ :=
          ((ℓ nr jm (embC wr))⁻¹ • (ℓ nr jm).comp killC).smulRight wr
        let ψr : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
          killC - embC.comp cr
        have hψr_kill (x : GaussianSpace ι_R ι_C) : ℓ nr jm (ψr x) = 0 := by
          simp only [ψr, cr, LinearMap.sub_apply, LinearMap.comp_apply,
            LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
          field_simp
          ring
        let ψ' (j : Fin d) : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
          if j = jm then ψr else ψ j
        refine ⟨insert nr D, ψ', ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hnr_notD, hDcard]
        · intro j hj
          by_cases hjm : j = jm
          · subst hjm; exact ⟨cr, fun x => by simp [ψ', ψr]⟩
          · simp only [ψ', hjm, ↓reduceIte]
            exact hψ_form j (by simp [jm, Fin.ext_iff] at hjm; omega)
        · intro n hn
          rcases Finset.mem_insert.mp hn with rfl | hnD
          · exact ⟨jm, by simp [jm], fun x => by simp [ψ', hψr_kill]⟩
          · obtain ⟨j, hj_lt, hkill⟩ := hDkill n hnD
            have hj_ne : j ≠ jm := by simp [jm, Fin.ext_iff]; omega
            exact ⟨j, by omega, fun x => by simp [ψ', hj_ne, hkill]⟩
    obtain ⟨D, ψ, hDcard, hψ_form, hDkill⟩ := hpeel (d - 2) le_rfl
    have hDcard_d : D.card = d := by omega
    have hdR : d ≤ R := by
      have := Finset.card_le_univ D
      simpa [hDcard_d] using this
    let φ (j : Fin d) : GaussianSpace ι_R ι_C →ₗ[ℝ] GaussianSpace ι_R ι_C :=
      if j = jLast then killC else ψ j
    let rem : Finset (Fin R) := Finset.univ \ D
    have hrem_card : Fintype.card rem = R - d := by
      rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ D),
        Finset.card_univ, Fintype.card_fin, hDcard_d]
    let eRem : Fin (R - d) ≃ rem := (Fintype.equivFinOfCardEq hrem_card).symm
    let ℓ' (m : Fin (R - d)) (j : Fin d) : GaussianSpace ι_R ι_C →ₗ[ℝ] ℝ :=
      (ℓ (eRem m).1 j).comp (φ j)
    have hrepr' (u : Fin d → GaussianSpace ι_R ι_C) :
        gaussianForm d S_R S_C α β u = ∑ m : Fin (R - d), ∏ j, ℓ' m j (u j) := by
      have hT : gaussianForm d S_R S_C α β u =
          gaussianForm d S_R (insert k₀ S_C) α β (fun j => φ j (u j)) := by
        simp only [gaussianForm, Finset.sum_insert hk₀]
        have hk0_zero : (β k₀ * ∏ j : Fin d, (φ j (u j)).2 k₀).re = 0 := by
          have hz : (φ jLast (u jLast)).2 k₀ = 0 := by simp [φ, killC]
          rw [Finset.prod_eq_zero (Finset.mem_univ jLast) hz, mul_zero, zero_re]
        rw [hk0_zero, zero_add]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          by_cases hj : j = jLast
          · subst hj; simp [φ, killC]
          · have hj_lt : (j : ℕ) < (d - 2) + 1 := by
              simp [jLast, Fin.ext_iff] at hj; omega
            obtain ⟨cj, hcj⟩ := hψ_form j hj_lt
            simp [φ, hj, hcj, killC, embC]
        · refine Finset.sum_congr rfl fun k hk => ?_
          have hne : k ≠ k₀ := fun h => hk₀ (h ▸ hk)
          congr 2
          refine Finset.prod_congr rfl fun j _ => ?_
          by_cases hj : j = jLast
          · subst hj; simp [φ, killC, hne]
          · have hj_lt : (j : ℕ) < (d - 2) + 1 := by
              simp [jLast, Fin.ext_iff] at hj; omega
            obtain ⟨cj, hcj⟩ := hψ_form j hj_lt
            simp [φ, hj, hcj, killC, embC, hne]
      rw [hT, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
      have hdead : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
        Finset.sum_eq_zero fun n hn => by
          obtain ⟨j, hj_lt, hkill⟩ := hDkill n hn
          have hj_ne : j ≠ jLast := by simp [jLast, Fin.ext_iff]; omega
          exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [φ, hj_ne, hkill])
      rw [hdead, add_zero]
      change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
      rw [← Finset.sum_coe_sort rem]
      exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
    have hle := ih (fun k hk => hβ k (Finset.mem_insert_of_mem hk)) ℓ' hrepr'
    rw [Finset.card_insert_of_notMem hk₀, mul_add, mul_one]
    omega

/-- Bundled `gaussianForm` as an `ℝ`-multilinear map. -/
noncomputable def gaussianMultilinearMap {ι_R ι_C : Type*} (d : ℕ)
    (S_R : Finset ι_R) (S_C : Finset ι_C) (α : ι_R → ℝ) (β : ι_C → ℂ) :
    MultilinearMap ℝ (fun _ : Fin d => GaussianSpace ι_R ι_C) ℝ :=
  (∑ i ∈ S_R, α i • (MultilinearMap.mkPiAlgebra ℝ (Fin d) ℝ).compLinearMap
    (fun _ => (LinearMap.proj (R := ℝ) i).comp (LinearMap.fst ℝ (ι_R → ℝ) (ι_C → ℂ)))) +
  ∑ k ∈ S_C,
    ({ toFun := fun z : ℂ => (β k * z).re
       map_add' := fun a b => by simp [mul_add]
       map_smul' := fun r a => by simp [Complex.real_smul, Complex.mul_re]; ring } :
      ℂ →ₗ[ℝ] ℝ).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℝ (Fin d) ℂ).compLinearMap
        (fun _ => (LinearMap.proj (R := ℝ) k).comp (LinearMap.snd ℝ (ι_R → ℝ) (ι_C → ℂ))))

lemma gaussianMultilinearMap_apply {ι_R ι_C : Type*} (d : ℕ)
    (S_R : Finset ι_R) (S_C : Finset ι_C) (α : ι_R → ℝ) (β : ι_C → ℂ)
    (u : Fin d → GaussianSpace ι_R ι_C) :
    gaussianMultilinearMap d S_R S_C α β u = gaussianForm d S_R S_C α β u := by
  simp [gaussianMultilinearMap, gaussianForm]

open scoped Classical in
/-- Exponential evaluation vectors span `GaussianSpace` over `ℝ` for distinct upper-half-plane
and real rates. -/
lemma span_gaussianEval_eq_top {ι : Type*} [Finite ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) :
    Submodule.span ℝ
      (Set.range fun s : ℝ≥0 =>
        ((fun i : {i : ι // (rate i).im = 0} => Real.exp ((rate i.1).re * (s : ℝ))),
         (fun k : {i : ι // 0 < (rate i).im} => exp (rate k.1 * (s : ℂ))))) = ⊤ := by
  cases nonempty_fintype ι
  let ι_R := {i : ι // (rate i).im = 0}
  let ι_C := {i : ι // 0 < (rate i).im}
  refine span_range_eq_top_of_dual fun L hL => ?_
  let a (i : ι_R) : ℝ := L (Pi.single i 1, 0)
  let b (k : ι_C) : ℂ :=
    L (0, Pi.single (M := fun _ => ℂ) k 1) - I * L (0, Pi.single (M := fun _ => ℂ) k I)
  have hL_expand (x : GaussianSpace ι_R ι_C) :
      L x = (∑ i : ι_R, a i * x.1 i) + ∑ k : ι_C, (b k * x.2 k).re := by
    have hx1 : x.1 = ∑ i : ι_R, x.1 i • Pi.single i (1 : ℝ) := by
      ext i₀; simp [Finset.sum_apply, Pi.single_apply]
    have hx2 : x.2 = ∑ k : ι_C,
        ((x.2 k).re • Pi.single (M := fun _ => ℂ) k (1 : ℂ) +
          (x.2 k).im • Pi.single (M := fun _ => ℂ) k I) := by
      ext k₀
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
        smul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
        Complex.real_smul, mul_one]
      exact (Complex.re_add_im (x.2 k₀)).symm
    have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
    conv_lhs => rw [hx, hx1, hx2]
    rw [map_add]
    congr 1
    · have hp : (∑ i : ι_R, x.1 i • Pi.single i (1 : ℝ), (0 : ι_C → ℂ)) =
          ∑ i : ι_R, x.1 i • (Pi.single i (1 : ℝ), (0 : ι_C → ℂ)) := by
        ext <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]
      rw [hp, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]
    · have hp : ((0 : ι_R → ℝ), ∑ k : ι_C,
          ((x.2 k).re • Pi.single (M := fun _ => ℂ) k (1 : ℂ) +
            (x.2 k).im • Pi.single (M := fun _ => ℂ) k I)) =
          ∑ k : ι_C, ((x.2 k).re • ((0 : ι_R → ℝ), Pi.single (M := fun _ => ℂ) k (1 : ℂ)) +
            (x.2 k).im • ((0 : ι_R → ℝ), Pi.single (M := fun _ => ℂ) k I)) := by
        ext <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum, Complex.real_smul]
      rw [hp, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp [b, Complex.mul_re]
      ring
  let ν : ι ⊕ ι_C → ℂ :=
    Sum.elim rate (fun k => starRingEnd ℂ (rate k.1))
  have hν : Function.Injective ν := injective_rates_with_conjugates hinj hup
  let cCoeff (i : ι) : ℂ :=
    if h : (rate i).im = 0 then (a ⟨i, h⟩ : ℂ)
    else (b ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩) / 2
  let P : ι ⊕ ι_C → ℂ[X] :=
    Sum.elim (fun i => C (cCoeff i)) (fun k => C (starRingEnd ℂ (b k) / 2))
  have hP0 : ∀ p, P p = 0 := by
    refine eq_zero_of_sum_expPoly_eq_zero' hν P fun u hu => ?_
    have hs := (hL_expand
      ((fun i : ι_R => Real.exp ((rate i.1).re * u)),
       (fun k : ι_C => exp (rate k.1 * (u : ℂ))))).symm.trans (hL ⟨u, hu.le⟩)
    dsimp only at hs
    have hsC : ((((∑ i : ι_R, a i * Real.exp ((rate i.1).re * u)) +
        ∑ k : ι_C, (b k * exp (rate k.1 * (u : ℂ))).re) : ℝ) : ℂ) = 0 := by
      rw [hs]; simp
    push_cast at hsC
    rw [← hsC]
    simp only [Fintype.sum_sum_type, P, ν, Sum.elim_inl, Sum.elim_inr, expPoly, eval_C]
    have hsplit_ι : (∑ i : ι, cCoeff i * exp (rate i * (u : ℂ))) =
        (∑ i : ι_R, (a i : ℂ) * exp (rate i.1 * (u : ℂ))) +
        ∑ k : ι_C, (b k / 2) * exp (rate k.1 * (u : ℂ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : ι => (rate i).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : ι => (rate i).im = 0)
          (Finset.univ.filter fun i : ι => (rate i).im = 0) (fun _ => by simp)
          (fun i => cCoeff i * exp (rate i * (u : ℂ)))]
        exact Finset.sum_congr rfl fun i _ => by simp [cCoeff, i.2]
      · have hiff (i : ι) : i ∈ Finset.univ.filter (fun i : ι => ¬ (rate i).im = 0) ↔
            0 < (rate i).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hup i) (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : ι => 0 < (rate i).im)
          (Finset.univ.filter fun i : ι => ¬ (rate i).im = 0) hiff
          (fun i => cCoeff i * exp (rate i * (u : ℂ)))]
        exact Finset.sum_congr rfl fun k _ => by simp [cCoeff, k.2.ne']
    rw [hsplit_ι, add_assoc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hrate_re : rate i.1 = ((rate i.1).re : ℂ) :=
        Complex.ext rfl (by simpa using i.2)
      rw [hrate_re]
      simp only [Complex.ofReal_re]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
      ring
  have ha0 (i : ι_R) : a i = 0 := by
    have hc := congrArg (fun q => (q.coeff 0).re) (hP0 (Sum.inl i.1))
    simpa [P, cCoeff, i.2] using hc
  have hb0 (k : ι_C) : b k = 0 := by
    have hc := congrArg (fun q => q.coeff 0) (hP0 (Sum.inl k.1))
    simp only [P, Sum.elim_inl, coeff_C_zero, coeff_zero, cCoeff, k.2.ne'] at hc
    exact (div_eq_zero_iff.mp hc).resolve_right two_ne_zero
  exact LinearMap.ext fun x => by simp [hL_expand, ha0, hb0]

open scoped Classical in
/-- **Exact `d`-way real radial rank of a multi-Gaussian representation (`d ≥ 2`).** -/
theorem separableRank_radial_gaussian_profile {d : ℕ} (hd : 2 ≤ d) {cs : List Component}
    (hcs : IsGaussianRepresentation cs) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      gaussianTotalCost d cs := by
  let comp : Fin cs.length → Component := fun i => cs[i]
  have hinj : Function.Injective fun i => (comp i).rate := by
    intro i j hij
    have h : (cs.map Component.rate)[(i : ℕ)]'(by simp) =
        (cs.map Component.rate)[(j : ℕ)]'(by simp) := by simpa [comp] using hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hcs.1.2).mp h)
  have hwf : ∀ i, (comp i).WellFormed := fun i => hcs.1.1 _ (List.getElem_mem _)
  have hg : ∀ i, (comp i).IsGaussian := fun i => hcs.2 _ (List.getElem_mem _)
  have hprof : (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      fun x => ∑ i : Fin cs.length, (comp i).eval (∑ j, x j ^ 2) := by
    funext x
    exact (Fin.sum_univ_fun_getElem cs fun c => c.eval (∑ j, x j ^ 2)).symm
  have hcost : gaussianTotalCost d cs = ∑ i : Fin cs.length, (comp i).gaussianCost d :=
    (Fin.sum_univ_fun_getElem cs (Component.gaussianCost d)).symm
  rw [hprof, hcost]
  refine le_antisymm ?_ ?_
  · exact iInf₂_le _ (IsSumOfProducts.finsetSum fun i =>
      isSumOfProducts_radial_gaussianComponent (by omega) (hwf i) (hg i))
  · rw [separableRank_radial_eq_hankel d
      (fun t => ∑ i : Fin cs.length, (comp i).eval t)]
    refine le_iInf₂ fun R hR => ?_
    let ι_R := {i : Fin cs.length // ((comp i).rate).im = 0}
    let ι_C := {i : Fin cs.length // 0 < ((comp i).rate).im}
    let α (i : ι_R) : ℝ := ((comp i.1).poly.coeff 0).re
    let β (k : ι_C) : ℂ := (comp k.1).poly.coeff 0
    let v (s : ℝ≥0) : GaussianSpace ι_R ι_C :=
      ((fun i => Real.exp (((comp i.1).rate).re * (s : ℝ))),
       (fun k => exp ((comp k.1).rate * (s : ℂ))))
    have hK_eq : (fun s : Fin d → ℝ≥0 => ∑ i : Fin cs.length, (comp i).eval (∑ j, (s j : ℝ))) =
        fun s => gaussianMultilinearMap d Finset.univ Finset.univ α β (fun j => v (s j)) := by
      funext s
      rw [gaussianMultilinearMap_apply]
      simp only [gaussianForm]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin cs.length => ((comp i).rate).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : Fin cs.length => ((comp i).rate).im = 0)
          (Finset.univ.filter fun i : Fin cs.length => ((comp i).rate).im = 0)
          (fun _ => by simp) (fun i => (comp i).eval (∑ j, (s j : ℝ)))]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hp : (comp i.1).poly = C ((comp i.1).poly.coeff 0) :=
          eq_C_of_natDegree_eq_zero (hg i.1)
        have hcoeff_im : ((comp i.1).poly.coeff 0).im = 0 := (hwf i.1).2.2 i.2 0
        have hrate : (comp i.1).rate = (((comp i.1).rate).re : ℂ) :=
          Complex.ext rfl (by simpa using i.2)
        have hcoeff : (comp i.1).poly.coeff 0 = (((comp i.1).poly.coeff 0).re : ℂ) :=
          Complex.ext rfl (by simpa using hcoeff_im)
        simp only [Component.eval, α, v]
        conv_lhs => rw [hp]
        rw [eval_C, hcoeff, hrate, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
          ← Complex.ofReal_mul, Complex.ofReal_re, Finset.mul_sum, Real.exp_sum]
        simp only [Complex.ofReal_re]
      · have hiff (i : Fin cs.length) :
            i ∈ Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0) ↔
              0 < ((comp i).rate).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hwf i).2.1 (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : Fin cs.length => 0 < ((comp i).rate).im)
          (Finset.univ.filter fun i : Fin cs.length => ¬ ((comp i).rate).im = 0)
          hiff (fun i => (comp i).eval (∑ j, (s j : ℝ)))]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hp : (comp k.1).poly = C ((comp k.1).poly.coeff 0) :=
          eq_C_of_natDegree_eq_zero (hg k.1)
        simp only [Component.eval, β, v, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
        conv_lhs => rw [hp]
        rw [eval_C]
    rw [hK_eq] at hR
    have hspan := span_gaussianEval_eq_top hinj (fun i => (hwf i).2.1)
    obtain ⟨ℓ, hℓ⟩ := exists_linear_factors_of_span_eq_top hspan
      (gaussianMultilinearMap d Finset.univ Finset.univ α β) hR
    simp_rw [gaussianMultilinearMap_apply] at hℓ
    have hα : ∀ i ∈ (Finset.univ : Finset ι_R), α i ≠ 0 := fun i _ h0 => by
      have hp : (comp i.1).poly = C ((comp i.1).poly.coeff 0) :=
        eq_C_of_natDegree_eq_zero (hg i.1)
      have hcoeff_im : ((comp i.1).poly.coeff 0).im = 0 := (hwf i.1).2.2 i.2 0
      have hc0 : (comp i.1).poly.coeff 0 = 0 := Complex.ext h0 hcoeff_im
      exact (hwf i.1).1 (hp.trans (by simp [hc0]))
    have hβ : ∀ k ∈ (Finset.univ : Finset ι_C), β k ≠ 0 := fun k _ h0 => by
      have hp : (comp k.1).poly = C ((comp k.1).poly.coeff 0) :=
        eq_C_of_natDegree_eq_zero (hg k.1)
      exact (hwf k.1).1 (hp.trans (by simp [β] at h0; simp [h0]))
    have hge := gaussianForm_rank_ge hd Finset.univ Finset.univ α β hα hβ ℓ hℓ
    have hsum_cost : (∑ i : Fin cs.length, (comp i).gaussianCost d) =
        (Finset.univ : Finset ι_R).card + d * (Finset.univ : Finset ι_C).card := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin cs.length => ((comp i).rate).im = 0)]
      congr 1
      · have hc1 : ∑ i ∈ Finset.univ.filter (fun i : Fin cs.length => ((comp i).rate).im = 0),
            (comp i).gaussianCost d =
            (Finset.univ.filter fun i : Fin cs.length => ((comp i).rate).im = 0).card := by
          trans ∑ _i ∈ Finset.univ.filter (fun i : Fin cs.length => ((comp i).rate).im = 0), 1
          · exact Finset.sum_congr rfl fun i hi => by
              simp [Component.gaussianCost, (Finset.mem_filter.mp hi).2]
          · simp
        rw [hc1, Finset.card_univ, Fintype.card_subtype]
      · have hcd : ∑ k ∈ Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0),
            (comp k).gaussianCost d =
            d * (Finset.univ.filter fun i : Fin cs.length => ¬ ((comp i).rate).im = 0).card := by
          trans ∑ _k ∈ Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0), d
          · exact Finset.sum_congr rfl fun k hk => by
              simp [Component.gaussianCost, (Finset.mem_filter.mp hk).2]
          · simp [mul_comm]
        have hf : Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0) =
            Finset.univ.filter (fun i : Fin cs.length => 0 < ((comp i).rate).im) :=
          Finset.filter_congr fun i _ =>
            ⟨fun h => lt_of_le_of_ne (hwf i).2.1 (Ne.symm h), fun h => h.ne'⟩
        rw [hcd, hf, Finset.card_univ, Fintype.card_subtype]
    rw [hsum_cost]
    exact_mod_cast hge

end KernelRank
