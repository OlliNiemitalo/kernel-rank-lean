import KernelRankLean.MultiComplexRank
import KernelRankLean.RealExpPoly

/-!
# Exact `d`-way real rank of radial exponential-polynomial kernels

In `d ≥ 2` coordinates:

* **Alternating root-of-unity formula (`re_prod_eq_sum_re`, `re_coeff_prod_eq_sum_re`).** For any
  `z₀, …, z_{d-1} ∈ ℂ`, `Re (∏ j, z j)` is a linear combination of `d` real products
  `∏ j, Re (z j · exp (-π i r / d))`. More generally, for complex polynomials `U_j` of degree at
  most `k` (`d ≥ 2`), `Re ([X^k] ∏ j, U_j(X))` is an alternating sum of `R = 2 * (d - 1) * k + d`
  real `d`-way products `∏ j, Re (U_j(exp (2π i r / R)) · exp (-π i r (2k + 1) / R))`.
* **Real Lagrange interpolation for real rates (`isSumOfProducts_radial_multiComponent`).** A
  real-rate component (`Im λ = 0`) of degree `k` splits into `(d - 1) * k + 1` real `d`-way
  products by interpolating `∏_{j ≥ 1} truncExpReal k (x_j²)` at `(d - 1) * k + 1` real nodes.
* **Exact `d`-way real rank for arbitrary representations (`separableRank_radial_profile`).**
  Alder–Strassen degree peeling over `ℝ` on `(∀ i, Fin (m_R i) → ℝ) × (∀ k, Fin (m_C k) → ℂ)`
  proves the matching lower bound `multiTotalCost d cs` (`(d - 1) * deg P + 1` per real rate and
  `2 * (d - 1) * deg P + d` per nonreal rate), specializing to `r + d · c` for multi-Gaussians and
  `totalCost cs` in `d = 2`.
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

/-- **Universal root-of-unity real decomposition for polynomial products (`d ≥ 2`, `k ≥ 0`).**
For complex polynomials `U₀, …, U_{d-1}` of degree at most `k`, `Re ([X^k] ∏ j, U_j(X))` is an
alternating sum of `R = 2 * (d - 1) * k + d` real `d`-way products. At `k = 0`, `R = d`,
recovering `re_prod_eq_sum_re` (`d ≥ 2`). -/
theorem re_coeff_prod_eq_sum_re {d : ℕ} (hd : 2 ≤ d) (k : ℕ)
    (U : Fin d → ℂ[X]) (hdeg : ∀ j, (U j).natDegree ≤ k) :
    ((∏ j : Fin d, U j).coeff k).re =
      (2 : ℝ) ^ (d - 1) / (2 * (d - 1) * k + d : ℕ) *
        ∑ r : Fin (2 * (d - 1) * k + d), (-1 : ℝ) ^ (r : ℕ) *
          ∏ j : Fin d,
            ((U j).eval (exp (2 * Real.pi * I * (r : ℕ) / (2 * (d - 1) * k + d : ℕ))) *
              exp (-Real.pi * I * (r : ℕ) * (2 * k + 1 : ℕ) /
                (2 * (d - 1) * k + d : ℕ))).re := by
  set R : ℕ := 2 * (d - 1) * k + d
  have hR_pos : 0 < R := by omega
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hR_pos.ne'
  let ζ (r : ℕ) : ℂ := exp (2 * Real.pi * I * r / R)
  let rot (r : ℕ) : ℂ := exp (-Real.pi * I * r * (2 * k + 1 : ℕ) / R)
  change ((∏ j : Fin d, U j).coeff k).re =
    (2 : ℝ) ^ (d - 1) / R *
      ∑ r : Fin R, (-1 : ℝ) ^ (r : ℕ) *
        ∏ j : Fin d, ((U j).eval (ζ (r : ℕ)) * rot (r : ℕ)).re
  have hU_eq (j : Fin d) : U j = ∑ q : Fin (k + 1), C ((U j).coeff q) * X ^ (q : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun q => C ((U j).coeff q) * X ^ q) (k + 1)]
    simpa [C_mul_X_pow_eq_monomial] using as_sum_range' (U j) (k + 1) (Nat.lt_succ_of_le (hdeg j))
  have hU_eval (j : Fin d) (z : ℂ) :
      (U j).eval z = ∑ q : Fin (k + 1), (U j).coeff q * z ^ (q : ℕ) := by
    conv_lhs => rw [hU_eq j]
    simp [eval_finsetSum]
  have hprod_coeff : (∏ j : Fin d, U j).coeff k =
      ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
        ∏ j : Fin d, (U j).coeff (q j) := by
    have hprod_expand : (∏ j : Fin d, U j) =
        ∑ q : Fin d → Fin (k + 1),
          C (∏ j : Fin d, (U j).coeff (q j)) * X ^ (∑ j : Fin d, (q j : ℕ)) := by
      have hlhs : (∏ j : Fin d, U j) =
          ∏ j : Fin d, ∑ q : Fin (k + 1), C ((U j).coeff q) * X ^ (q : ℕ) :=
        Finset.prod_congr rfl fun j _ => hU_eq j
      rw [hlhs, Fintype.prod_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.prod_mul_distrib, ← map_prod C, Finset.prod_pow_eq_pow_sum]
    rw [hprod_expand, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext q
    simp [eq_comm]
  rw [hprod_coeff]
  apply Complex.ofReal_inj.mp
  push_cast
  have hre (w : ℂ) : (w.re : ℂ) = (starRingEnd ℂ w + w) / 2 := by
    rw [Complex.re_eq_add_conj]; ring
  simp_rw [hre, hU_eval]
  have hconj_term (j : Fin d) (r : ℕ) :
      starRingEnd ℂ ((∑ q : Fin (k + 1), (U j).coeff q * ζ r ^ (q : ℕ)) * rot r) =
        ∑ q : Fin (k + 1),
          starRingEnd ℂ ((U j).coeff q) *
            exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R) := by
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_assoc, map_mul]
    congr 1
    simp only [ζ, rot, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_conj]
    congr 1
    push_cast
    simp only [map_add, map_mul, map_neg, map_div₀, map_ofNat, map_one, Complex.conj_ofReal,
      Complex.conj_I, Complex.conj_natCast]
    field_simp
    ring
  have hplain_term (j : Fin d) (r : ℕ) :
      (∑ q : Fin (k + 1), (U j).coeff q * ζ r ^ (q : ℕ)) * rot r =
        ∑ q : Fin (k + 1),
          (U j).coeff q *
            exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_assoc]
    congr 1
    simp only [ζ, rot, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hconj_term, hplain_term]
  have hprod_r (r : ℕ) :
      (∏ j : Fin d,
        ((∑ q : Fin (k + 1),
            starRingEnd ℂ ((U j).coeff q) *
              exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) +
          ∑ q : Fin (k + 1),
            (U j).coeff q *
              exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) / 2) =
      ((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1),
            (∏ j : Fin d, if j ∈ S then starRingEnd ℂ ((U j).coeff (q j))
              else (U j).coeff (q j)) *
            exp (Real.pi * I * r *
              (∑ j : Fin d, if j ∈ S then (((2 * k + 1 : ℕ) : ℤ) - 2 * (q j : ℕ))
                else (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q j : ℕ))) / R) := by
    have hdiv :
        (∏ j : Fin d,
          ((∑ q : Fin (k + 1),
              starRingEnd ℂ ((U j).coeff q) *
                exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) +
            ∑ q : Fin (k + 1),
              (U j).coeff q *
                exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) / 2) =
        ∏ j : Fin d,
          ((∑ q : Fin (k + 1),
              starRingEnd ℂ ((U j).coeff q) *
                exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) +
            ∑ q : Fin (k + 1),
              (U j).coeff q *
                exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) *
            (2 : ℂ)⁻¹ :=
      Finset.prod_congr rfl fun _ _ => div_eq_mul_inv _ 2
    rw [hdiv, Finset.prod_mul_distrib]
    have h2 : (∏ _j : Fin d, (2 : ℂ)⁻¹) = ((2 : ℂ) ^ d)⁻¹ := by simp
    rw [h2, mul_comm _ (((2 : ℂ) ^ d)⁻¹)]
    congr 1
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hsub : S ⊆ Finset.univ := Finset.mem_powerset.mp hS
    have hmerge :
        (∏ j ∈ S, ∑ q : Fin (k + 1),
          starRingEnd ℂ ((U j).coeff q) *
            exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) *
        (∏ j ∈ Finset.univ \ S, ∑ q : Fin (k + 1),
          (U j).coeff q *
            exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) =
        ∏ j : Fin d, ∑ q : Fin (k + 1),
          (if j ∈ S then starRingEnd ℂ ((U j).coeff q) else (U j).coeff q) *
          exp (Real.pi * I * r *
            (if j ∈ S then (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ))
             else (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ))) / R) := by
      rw [← Finset.prod_sdiff hsub, mul_comm]
      congr 1
      · refine Finset.prod_congr rfl fun j hj => Finset.sum_congr rfl fun q _ => ?_
        have hjn : j ∉ S := (Finset.mem_sdiff.mp hj).2
        simp [hjn]
      · refine Finset.prod_congr rfl fun j hj => Finset.sum_congr rfl fun q _ => ?_
        simp [hj]
    rw [hmerge, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
  simp_rw [hprod_r]
  let Z (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) : ℂ :=
    ∏ j : Fin d, if j ∈ S then starRingEnd ℂ ((U j).coeff (q j)) else (U j).coeff (q j)
  let E (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) : ℤ :=
    ∑ j : Fin d, if j ∈ S then (((2 * k + 1 : ℕ) : ℤ) - 2 * (q j : ℕ))
      else (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q j : ℕ))
  change _ = (2 : ℂ) ^ (d - 1) * (R : ℂ)⁻¹ *
    ∑ r : Fin R, (-1 : ℂ) ^ (r : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q * exp (Real.pi * I * (r : ℕ) * (E S q) / R))
  have hpull :
      ∑ r : Fin R, (-1 : ℂ) ^ (r : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1), Z S q * exp (Real.pi * I * (r : ℕ) * (E S q) / R)) =
      ((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1), Z S q *
            ∑ r ∈ Finset.range R, (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ => (-1 : ℂ) ^ r * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1), Z S q * exp (Real.pi * I * r * (E S q) / R))) R]
    simp_rw [← mul_assoc ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹),
      mul_comm ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹), mul_assoc (((2 : ℂ) ^ d)⁻¹), ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring
  rw [hpull]
  have hR_int : (R : ℤ) = 2 * ((d : ℤ) - 1) * (k : ℤ) + (d : ℤ) := by
    have hd_sub : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := Int.ofNat_sub (by omega)
    dsimp [R]
    push_cast [hd_sub]
    ring
  have hE_eq (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) :
      (R : ℤ) + E S q =
        2 * ((2 * (k : ℤ) + 1) * (S.card : ℤ) +
          (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) -
          (∑ j ∈ S, ((q j : ℕ) : ℤ)) - (k : ℤ)) := by
    have hsplit_E : E S q =
        (∑ j ∈ S, (((2 * k + 1 : ℕ) : ℤ) - 2 * (q j : ℕ))) +
        (∑ j ∈ Finset.univ \ S, (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q j : ℕ))) := by
      dsimp [E]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
      have hf1 : Finset.univ.filter (· ∈ S) = S := by ext j; simp
      have hf2 : Finset.univ.filter (fun j => j ∉ S) = Finset.univ \ S := by ext j; simp
      rw [hf1, hf2]
      congr 1
      · exact Finset.sum_congr rfl fun j hj => by simp [hj]
      · exact Finset.sum_congr rfl fun j hj => by simp [(Finset.mem_sdiff.mp hj).2]
    have hcard_sdiff : (Finset.univ \ S).card = d - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
    have hcard_le : S.card ≤ d := by simpa using Finset.card_le_univ S
    rw [hsplit_E, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, hcard_sdiff, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [nsmul_eq_mul]
    have hsub_int : ((d - S.card : ℕ) : ℤ) = (d : ℤ) - S.card := Int.ofNat_sub hcard_le
    rw [hR_int, hsub_int]
    push_cast
    ring
  have hinner (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) :
      (∑ r ∈ Finset.range R, (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R)) =
        if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0 := by
    let K : ℤ := (2 * (k : ℤ) + 1) * (S.card : ℤ) +
      (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) - (∑ j ∈ S, ((q j : ℕ) : ℤ)) - (k : ℤ)
    let w : ℂ := exp (2 * Real.pi * I * K / R)
    have hterm (r : ℕ) :
        (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R) = w ^ r := by
      have hm1 : (-1 : ℂ) ^ r = exp (Real.pi * I * r) := by
        rw [mul_comm (Real.pi * I) (r : ℂ), exp_nat_mul, exp_pi_mul_I]
      rw [hm1, ← exp_add, ← exp_nat_mul]
      congr 1
      have hEK : (E S q : ℂ) = 2 * (K : ℂ) - (R : ℂ) := by
        have := congrArg (Int.cast (R := ℂ)) (hE_eq S q)
        dsimp [K]
        push_cast at this ⊢
        linear_combination this
      rw [hEK]
      field_simp
      ring
    simp_rw [hterm]
    have hsum_S_le : (∑ j ∈ S, ((q j : ℕ) : ℤ)) ≤ S.card * (k : ℤ) := by
      calc (∑ j ∈ S, ((q j : ℕ) : ℤ)) ≤ ∑ _j ∈ S, (k : ℤ) :=
            Finset.sum_le_sum fun j _ => by exact_mod_cast Nat.lt_succ_iff.mp (q j).2
        _ = S.card * (k : ℤ) := by simp
    have hsum_S_nonneg : 0 ≤ ∑ j ∈ S, ((q j : ℕ) : ℤ) :=
      Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
    have hsum_c_le : (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) ≤ (d - S.card : ℕ) * (k : ℤ) := by
      have hcard_sdiff : (Finset.univ \ S).card = d - S.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
      calc (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) ≤ ∑ _j ∈ Finset.univ \ S, (k : ℤ) :=
            Finset.sum_le_sum fun j _ => by exact_mod_cast Nat.lt_succ_iff.mp (q j).2
        _ = (d - S.card : ℕ) * (k : ℤ) := by simp [hcard_sdiff]
    have hsum_c_nonneg : 0 ≤ ∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ) :=
      Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
    have hd_int : 2 ≤ (d : ℤ) := by exact_mod_cast hd
    have hk_int : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
    split_ifs with hcond
    · rcases hcond with ⟨rfl | rfl, hsum_k⟩
      · have hK0 : K = 0 := by
          have hq_int : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by exact_mod_cast hsum_k
          dsimp [K]
          simp [hq_int]
        simp [w, hK0]
      · have hKR : K = R := by
          have hq_int : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by exact_mod_cast hsum_k
          dsimp [K]
          simp only [Fintype.card_fin, Finset.sdiff_self, Finset.sum_empty, add_zero, hq_int]
          rw [hR_int]
          ring
        have hw1 : w = 1 := by
          simp only [w, hKR, Int.cast_natCast]
          have : 2 * Real.pi * I * (R : ℂ) / (R : ℂ) = 2 * Real.pi * I := by field_simp
          rw [this, exp_two_pi_mul_I]
        simp [hw1]
    · have hwR : w ^ R = 1 := by
        rw [← exp_nat_mul]
        have hexp : (R : ℂ) * (2 * Real.pi * I * (K : ℂ) / R) =
            (K : ℂ) * (2 * Real.pi * I) := by field_simp
        rw [hexp]
        simp [exp_int_mul_two_pi_mul_I]
      have hw1 : w ≠ 1 := by
        intro h1
        rw [exp_eq_one_iff] at h1
        obtain ⟨m, hm⟩ := h1
        have hpi : (2 : ℂ) * Real.pi * I ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            I_ne_zero
        have heq : (K : ℂ) = (m : ℂ) * R := by
          apply mul_right_cancel₀ hpi
          have hm' : 2 * Real.pi * I * (K : ℂ) = (m : ℂ) * (2 * Real.pi * I) * R :=
            (div_eq_iff hR0).mp hm
          linear_combination hm'
        have hz : K = m * R := by exact_mod_cast heq
        have hcard_le : S.card ≤ d := by simpa using Finset.card_le_univ S
        by_cases hSu : S = ∅ ∨ S = Finset.univ
        · have hne_k : ∑ j, (q j : ℕ) ≠ k := fun hk => hcond ⟨hSu, hk⟩
          rcases hSu with rfl | rfl
          · have hK_val : K = (∑ j : Fin d, ((q j : ℕ) : ℤ)) - k := by
              dsimp [K]; simp
            have hsum_ub : (∑ j : Fin d, ((q j : ℕ) : ℤ)) ≤ d * (k : ℤ) := by
              simpa using hsum_c_le
            have hsum_lb : 0 ≤ ∑ j : Fin d, ((q j : ℕ) : ℤ) := by simpa using hsum_c_nonneg
            have hK_ne0 : K ≠ 0 := by
              intro h0
              apply hne_k
              have : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by omega
              exact_mod_cast this
            have hm_ne0 : m ≠ 0 := by rintro rfl; exact hK_ne0 (by omega)
            rcases lt_or_gt_of_ne hm_ne0 with hm_neg | hm_pos
            · have : m * (R : ℤ) ≤ -1 * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
            · have : 1 * (R : ℤ) ≤ m * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
          · have hK_val : K = (R : ℤ) + k - ∑ j : Fin d, ((q j : ℕ) : ℤ) := by
              dsimp [K]
              simp only [Fintype.card_fin, Finset.sdiff_self, Finset.sum_empty, add_zero]
              rw [hR_int]
              ring
            have hsum_ub : (∑ j : Fin d, ((q j : ℕ) : ℤ)) ≤ d * (k : ℤ) := by
              simpa using hsum_S_le
            have hsum_lb : 0 ≤ ∑ j : Fin d, ((q j : ℕ) : ℤ) := by simpa using hsum_S_nonneg
            have hK_neR : K ≠ R := by
              intro hR_eq
              apply hne_k
              have : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by omega
              exact_mod_cast this
            have hm_ne1 : m ≠ 1 := by rintro rfl; exact hK_neR (by omega)
            rcases lt_or_gt_of_ne hm_ne1 with hm_le0 | hm_ge2
            · have : m * (R : ℤ) ≤ 0 * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
            · have : 2 * (R : ℤ) ≤ m * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
        · push Not at hSu
          have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr hSu.1
          have hS_lt : S.card ≤ d - 1 := by
            have hlt : S.card < d := by
              simpa using Finset.card_lt_card
                (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hSu.2⟩)
            omega
          have hS_pos_int : 1 ≤ (S.card : ℤ) := by exact_mod_cast hS_pos
          have hS_lt_int : (S.card : ℤ) ≤ (d : ℤ) - 1 := by omega
          have hK_pos : 1 ≤ K := by
            dsimp [K]
            nlinarith
          have hK_lt : K ≤ (R : ℤ) - 1 := by
            have hsub_int : ((d - S.card : ℕ) : ℤ) = (d : ℤ) - S.card := Int.ofNat_sub hcard_le
            rw [hsub_int] at hsum_c_le
            dsimp [K]
            nlinarith [hR_int]
          rcases le_or_gt m 0 with hm_le0 | hm_ge1
          · have : m * (R : ℤ) ≤ 0 :=
              Int.mul_nonpos_of_nonpos_of_nonneg hm_le0 (Int.natCast_nonneg R)
            omega
          · have : 1 * (R : ℤ) ≤ m * (R : ℤ) :=
              Int.mul_le_mul_of_nonneg_right hm_ge1 (Int.natCast_nonneg R)
            omega
      have hgeom := geom_sum_mul w R
      rw [hwR, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw1)
  have hsumZ :
      (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q *
          ∑ r ∈ Finset.range R, (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R)) =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q *
          if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0 :=
    Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun q _ => by rw [hinner S q]
  rw [hsumZ]
  have hsplit_S :
      (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q *
          if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
        Z ∅ q * R) +
      (∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
        Z Finset.univ q * R) := by
    have hcond_split (S : Finset (Fin d)) :
        (∑ q : Fin d → Fin (k + 1), Z S q *
          if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0) =
        if S = ∅ ∨ S = Finset.univ then
          ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
            Z S q * R
        else 0 := by
      by_cases hS : S = ∅ ∨ S = Finset.univ
      · simp [hS, mul_ite, ← Finset.sum_filter]
      · simp [hS]
    simp_rw [hcond_split, ← Finset.sum_filter]
    have hfilt : (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => S = ∅ ∨ S = Finset.univ) = {∅, Finset.univ} := by
      ext S; simp
    have hne : (∅ : Finset (Fin d)) ≠ Finset.univ := by
      intro h; have := congrArg Finset.card h; simp at this; omega
    rw [hfilt, Finset.sum_pair hne]
  rw [hsplit_S, ← Finset.sum_mul, ← Finset.sum_mul]
  have hZ0 (q : Fin d → Fin (k + 1)) : Z ∅ q = ∏ j, (U j).coeff (q j) := by simp [Z]
  have hZ1 (q : Fin d → Fin (k + 1)) :
      Z Finset.univ q = starRingEnd ℂ (∏ j, (U j).coeff (q j)) := by
    simp [Z, map_prod]
  simp_rw [hZ0, hZ1]
  rw [← map_sum (starRingEnd ℂ)]
  have hpow2 : (2 : ℂ) ^ d = (2 : ℂ) ^ (d - 1) * 2 := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  have h2ne : (2 : ℂ) ^ (d - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hpow2]
  field_simp
  ring

/-- Every well-formed component `c` has `d`-way real radial separable rank at most
`c.multiCost d` (`d ≥ 2`). -/
lemma isSumOfProducts_radial_multiComponent {d : ℕ} (hd : 2 ≤ d) {c : Component}
    (hwf : c.WellFormed) :
    IsSumOfProducts (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2)) (c.multiCost d) := by
  let k := c.poly.natDegree
  have hd0 : 0 < d := by omega
  let j₀ : Fin d := ⟨0, hd0⟩
  let rest : Finset (Fin d) := Finset.univ.erase j₀
  by_cases him : c.rate.im = 0
  · -- Real rate: Lagrange interpolation over `ℝ` at `0, 1, …, L - 1` (`L = (d - 1) * k + 1`).
    simp only [Component.multiCost, him, ↓reduceIte]
    set L : ℕ := (d - 1) * k + 1
    let P_R : ℝ[X] := ∑ q ∈ Finset.range (k + 1), C (c.poly.coeff q).re * X ^ q
    have hmap_P : P_R.map (algebraMap ℝ ℂ) = c.poly := by
      conv_rhs => rw [as_sum_range' c.poly (k + 1) (Nat.lt_succ_self k)]
      simp only [P_R, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, ← C_mul_X_pow_eq_monomial]
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 2
      exact Complex.ext rfl (hwf.2.2 him q).symm
    have hdeg_PR : P_R.natDegree ≤ k := by
      have : (P_R.map (algebraMap ℝ ℂ)).natDegree = P_R.natDegree :=
        natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective P_R
      rw [← this, hmap_P]
    let truncR (u : ℝ) : ℝ[X] :=
      ∑ q ∈ Finset.range (k + 1), C (u ^ q / (q.factorial : ℝ)) * X ^ q
    have hmap_trunc (u : ℝ) : (truncR u).map (algebraMap ℝ ℂ) = truncExpPoly k (u : ℂ) := by
      simp [truncR, truncExpPoly, Polynomial.map_sum]
    have hdeg_trunc (u : ℝ) : (truncR u).natDegree ≤ k := by
      rw [← natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective (truncR u), hmap_trunc]
      exact natDegree_truncExpPoly_le k (u : ℂ)
    let nodes (r : Fin L) : ℝ := (r : ℕ)
    have hinj_nodes : Set.InjOn nodes ↑(Finset.univ : Finset (Fin L)) := by
      intro a _ b _ hab
      exact Fin.ext (Nat.cast_inj.mp hab)
    let B (r : Fin L) : ℝ[X] := Lagrange.basis Finset.univ nodes r
    let f (r : Fin L) (j : Fin d) (u : ℝ) : ℝ :=
      if j = j₀ then
        (∑ q ∈ Finset.range (k + 1),
          (q.factorial : ℝ) * (B r).coeff q * (hasseDeriv q P_R).eval (u ^ 2)) *
          Real.exp (c.rate.re * u ^ 2)
      else
        (truncR (u ^ 2)).eval (nodes r) * Real.exp (c.rate.re * u ^ 2)
    refine ⟨f, fun x => ?_⟩
    dsimp only
    have heval_c : c.eval (∑ j, x j ^ 2) =
        P_R.eval (∑ j, x j ^ 2) * Real.exp (c.rate.re * ∑ j, x j ^ 2) := by
      have hrate : c.rate = (c.rate.re : ℂ) := Complex.ext rfl (by simpa using him)
      have heval_PR (t : ℝ) : c.poly.eval (t : ℂ) = ((P_R.eval t : ℝ) : ℂ) := by
        rw [← hmap_P]
        simp [P_R, eval_finsetSum]
      unfold Component.eval
      rw [heval_PR, hrate, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      simp only [Complex.ofReal_re]
    let A : ℝ[X] := ∏ j ∈ rest, truncR (x j ^ 2)
    have hdeg_A : A.degree < (Finset.univ : Finset (Fin L)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr ?_)
      have hmap_A : A.map (algebraMap ℝ ℂ) = ∏ j ∈ rest, truncExpPoly k (x j ^ 2 : ℂ) := by
        simp [A, Polynomial.map_prod, hmap_trunc]
      have hle : A.natDegree ≤ rest.card * k := by
        rw [← natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective A, hmap_A]
        exact natDegree_prod_truncExpPoly_le rest k (fun j => (x j ^ 2 : ℂ))
      have hcard_rest : rest.card = d - 1 := by simp [rest]
      rw [hcard_rest] at hle
      dsimp [L]; omega
    have hA_interp : A = ∑ r : Fin L, C (A.eval (nodes r)) * B r := by
      have h := Lagrange.eq_interpolate hinj_nodes hdeg_A
      rwa [Lagrange.interpolate_apply] at h
    have hA_coeff (q : ℕ) (hq : q ≤ k) :
        (∑ j ∈ rest, x j ^ 2) ^ q =
          (q.factorial : ℝ) * ∑ r : Fin L, (B r).coeff q * A.eval (nodes r) := by
      have hcC := coeff_prod_truncExpPoly rest k (fun j => (x j ^ 2 : ℂ)) hq
      have hmap_A : A.map (algebraMap ℝ ℂ) = ∏ j ∈ rest, truncExpPoly k (x j ^ 2 : ℂ) := by
        simp [A, Polynomial.map_prod, hmap_trunc]
      have hcast : (∑ j ∈ rest, (x j : ℂ) ^ 2) ^ q / (q.factorial : ℂ) =
          (((∑ j ∈ rest, x j ^ 2) ^ q / (q.factorial : ℝ) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [← hmap_A, coeff_map] at hcC
      have hcC' : (A.coeff q : ℂ) = (((∑ j ∈ rest, x j ^ 2) ^ q / (q.factorial : ℝ) : ℝ) : ℂ) :=
        hcC.trans hcast
      have hcR : A.coeff q = (∑ j ∈ rest, x j ^ 2) ^ q / (q.factorial : ℝ) :=
        Complex.ofReal_inj.mp hcC'
      have hfq : (q.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.factorial_ne_zero
      have hpow : (∑ j ∈ rest, x j ^ 2) ^ q = (q.factorial : ℝ) * A.coeff q := by
        rw [hcR]; field_simp
      conv_lhs => rw [hpow, hA_interp, finsetSum_coeff]
      congr 1
      exact Finset.sum_congr rfl fun r _ => by rw [coeff_C_mul, mul_comm]
    have htaylor : P_R.eval (∑ j : Fin d, x j ^ 2) =
        ∑ q ∈ Finset.range (k + 1),
          (hasseDeriv q P_R).eval (x j₀ ^ 2) * (∑ j ∈ rest, x j ^ 2) ^ q := by
      have hsum_x : x j₀ ^ 2 + ∑ j ∈ rest, x j ^ 2 = ∑ j : Fin d, x j ^ 2 :=
        Finset.add_sum_erase Finset.univ (fun j => x j ^ 2) (Finset.mem_univ j₀)
      rw [← hsum_x, add_comm (x j₀ ^ 2), ← taylor_eval,
        eval_eq_sum_range' (by rw [natDegree_taylor]; exact Nat.lt_succ_of_le hdeg_PR)]
      exact Finset.sum_congr rfl fun q _ => by rw [taylor_coeff]
    have hPR_sum : P_R.eval (∑ j : Fin d, x j ^ 2) =
        ∑ r : Fin L,
          (∑ q ∈ Finset.range (k + 1),
            (q.factorial : ℝ) * (B r).coeff q * (hasseDeriv q P_R).eval (x j₀ ^ 2)) *
          ∏ j ∈ rest, (truncR (x j ^ 2)).eval (nodes r) := by
      rw [htaylor]
      have hstep : ∑ q ∈ Finset.range (k + 1),
          (hasseDeriv q P_R).eval (x j₀ ^ 2) * (∑ j ∈ rest, x j ^ 2) ^ q =
          ∑ q ∈ Finset.range (k + 1), ∑ r : Fin L,
            (q.factorial : ℝ) * (B r).coeff q * (hasseDeriv q P_R).eval (x j₀ ^ 2) *
              A.eval (nodes r) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [hA_coeff q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)),
          ← mul_assoc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hstep, Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_mul, eval_prod]
    rw [heval_c, hPR_sum, Finset.sum_mul, Finset.mul_sum, Real.exp_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ (fun j => Real.exp (c.rate.re * x j ^ 2))
        (Finset.mem_univ j₀)]
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have her : ∏ j ∈ rest, f r j (x j) =
        (∏ j ∈ rest, (truncR (x j ^ 2)).eval (nodes r)) *
          ∏ j ∈ rest, Real.exp (c.rate.re * x j ^ 2) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j hj => by simp [f, Finset.ne_of_mem_erase hj]
    rw [her]
    simp only [f, ↓reduceIte]
    ring
  · -- Nonreal rate: apply `re_coeff_prod_eq_sum_re` with `R = 2 * (d - 1) * k + d`.
    simp only [Component.multiCost, him, ↓reduceIte]
    set R : ℕ := 2 * (d - 1) * k + d
    let U_of (x : ℝ) (j : Fin d) : ℂ[X] :=
      C (exp (c.rate * (x ^ 2 : ℝ))) *
        if j = j₀ then revHassePoly c.poly k (x ^ 2 : ℝ) else truncExpPoly k (x ^ 2 : ℝ)
    let ζ (r : Fin R) : ℂ := exp (2 * Real.pi * I * (r : ℕ) / R)
    let rot (r : Fin R) : ℂ := exp (-Real.pi * I * (r : ℕ) * (2 * k + 1 : ℕ) / R)
    let f (r : Fin R) (j : Fin d) (u : ℝ) : ℝ :=
      if j = j₀ then
        (2 : ℝ) ^ (d - 1) / R * (-1 : ℝ) ^ (r : ℕ) * ((U_of u j).eval (ζ r) * rot r).re
      else
        ((U_of u j).eval (ζ r) * rot r).re
    refine ⟨f, fun x => ?_⟩
    dsimp only
    have hdeg_U (j : Fin d) : (U_of (x j) j).natDegree ≤ k := by
      dsimp [U_of]
      refine natDegree_C_mul_le _ _ |>.trans ?_
      split_ifs
      · exact natDegree_revHassePoly_le c.poly k (x j ^ 2 : ℝ)
      · exact natDegree_truncExpPoly_le k (x j ^ 2 : ℝ)
    have hprod_U : ((∏ j : Fin d, U_of (x j) j).coeff k).re = c.eval (∑ j, x j ^ 2) := by
      have hpull_C : (∏ j : Fin d, U_of (x j) j) =
          C (exp (c.rate * (∑ j : Fin d, x j ^ 2 : ℝ))) *
            (revHassePoly c.poly k (x j₀ ^ 2 : ℝ) *
              ∏ j ∈ rest, truncExpPoly k (x j ^ 2 : ℝ)) := by
        dsimp [U_of]
        rw [Finset.prod_mul_distrib, ← map_prod C, ← Complex.exp_sum, ← Finset.mul_sum,
          ← Complex.ofReal_sum]
        congr 1
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
        simp only [↓reduceIte]
        congr 1
        exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
      rw [hpull_C, coeff_C_mul,
        coeff_revHassePoly_mul_prod_truncExpPoly c.poly j₀ (fun j => ((x j ^ 2 : ℝ) : ℂ))]
      simp only [Component.eval, Complex.ofReal_sum, mul_comm]
    rw [← hprod_U, re_coeff_prod_eq_sum_re hd k (fun j => U_of (x j) j) hdeg_U, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => ((U_of (x j) j).eval (ζ r) * rot r).re) (Finset.mem_univ j₀)]
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have her : ∏ j ∈ rest, f r j (x j) =
        ∏ j ∈ rest, ((U_of (x j) j).eval (ζ r) * rot r).re :=
      Finset.prod_congr rfl fun j hj => by simp [f, Finset.ne_of_mem_erase hj]
    rw [her]
    simp only [f, ↓reduceIte]
    ring


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



/-- Space of real-rate and nonreal-rate Taylor coefficients. -/
abbrev RealExpSpace {ι_R ι_C : Type*} (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) : Type _ :=
  (∀ i, Fin (m_R i) → ℝ) × (∀ k, Fin (m_C k) → ℂ)

/-- Space of nonreal-rate complex Taylor coefficients. -/
abbrev CplxExpSpace {ι_C : Type*} (m_C : ι_C → ℕ) : Type _ :=
  ∀ k, Fin (m_C k) → ℂ

/-- Single real coordinate vector in `∀ i, Fin (m i) → ℝ`. -/
def singleRealCoeff {ι : Type*} [DecidableEq ι] {m : ι → ℕ} (i₀ : ι) (q₀ : Fin (m i₀))
    (a : ℝ) : ∀ i, Fin (m i) → ℝ :=
  fun i q => if h : i = i₀ then if h ▸ q = q₀ then a else 0 else 0

@[simp]
lemma singleRealCoeff_same {ι : Type*} [DecidableEq ι] {m : ι → ℕ} (i₀ : ι) (q₀ : Fin (m i₀))
    (a : ℝ) : singleRealCoeff i₀ q₀ a i₀ q₀ = a := by
  simp [singleRealCoeff]

lemma singleRealCoeff_of_ne_idx {ι : Type*} [DecidableEq ι] {m : ι → ℕ} {i : ι} (i₀ : ι)
    (q₀ : Fin (m i₀)) (a : ℝ) (hi : i ≠ i₀) (q : Fin (m i)) :
    singleRealCoeff i₀ q₀ a i q = 0 := by
  simp [singleRealCoeff, hi]

lemma singleRealCoeff_of_ne_deg {ι : Type*} [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (q₀ q : Fin (m i₀)) (a : ℝ) (hq : q ≠ q₀) :
    singleRealCoeff i₀ q₀ a i₀ q = 0 := by
  simp [singleRealCoeff, hq]

/-- Embedding `ℝ` into slot `(i₀, q₀)` of `RealExpSpace m_R m_C`. -/
def embRealCoeff {ι_R ι_C : Type*} [DecidableEq ι_R] {m_R : ι_R → ℕ} {m_C : ι_C → ℕ}
    (i₀ : ι_R) (q₀ : Fin (m_R i₀)) : ℝ →ₗ[ℝ] RealExpSpace m_R m_C where
  toFun a := (singleRealCoeff i₀ q₀ a, 0)
  map_add' a b := by
    ext i q
    · by_cases hi : i = i₀
      · subst hi
        by_cases hq : q = q₀ <;> simp [singleRealCoeff, hq]
      · simp [singleRealCoeff, hi]
    · simp
  map_smul' r a := by
    ext i q
    · by_cases hi : i = i₀
      · subst hi
        by_cases hq : q = q₀ <;> simp [singleRealCoeff, hq]
      · simp [singleRealCoeff, hi]
    · simp

/-- Embedding `ℂ` (`ℝ`-linearly) into slot `(k₀, q₀)` of `CplxExpSpace m_C`. -/
noncomputable def embCplxCoeff {ι_C : Type*} [DecidableEq ι_C] {m_C : ι_C → ℕ}
    (k₀ : ι_C) (q₀ : Fin (m_C k₀)) : ℂ →ₗ[ℝ] CplxExpSpace m_C where
  toFun z := singleCoeff k₀ q₀ z
  map_add' a b := by
    ext k q
    by_cases hk : k = k₀
    · subst hk
      by_cases hq : q = q₀ <;> simp [singleCoeff, hq]
    · simp [singleCoeff, hk]
  map_smul' r a := by
    ext k q
    by_cases hk : k = k₀
    · subst hk
      by_cases hq : q = q₀ <;> simp [singleCoeff, hq, Complex.real_smul]
    · simp [singleCoeff, hk]

/-- Real truncated-convolution multilinear form on `∀ i, Fin (m_R i) → ℝ`. -/
noncomputable def realTruncForm {ι_R : Type*} [Fintype ι_R] (d : ℕ) (m_R c_R : ι_R → ℕ)
    (w_R : ι_R → ℕ → ℝ) (u : Fin d → ∀ i, Fin (m_R i) → ℝ) : ℝ :=
  ∑ i : ι_R, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i),
    w_R i (∑ j, (q j : ℕ)) * ∏ j : Fin d, u j i (q j)

/-- Complex-rate real-part truncated-convolution form on `CplxExpSpace m_C`. -/
noncomputable def cplxTruncForm {ι_C : Type*} [Fintype ι_C] (d : ℕ) (m_C c_C : ι_C → ℕ)
    (w_C : ι_C → ℕ → ℂ) (u : Fin d → CplxExpSpace m_C) : ℝ :=
  ∑ k : ι_C, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c_C k),
    (w_C k (∑ j, (q j : ℕ)) * ∏ j : Fin d, u j k (q j)).re

/-- Combined real-and-complex truncated-convolution form on `RealExpSpace m_R m_C`. -/
noncomputable def realExpForm {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C]
    (d : ℕ) (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_R : ι_R → ℕ) (c_C : ι_C → ℕ)
    (w_R : ι_R → ℕ → ℝ) (w_C : ι_C → ℕ → ℂ)
    (u : Fin d → RealExpSpace m_R m_C) : ℝ :=
  realTruncForm d m_R c_R w_R (fun j => (u j).1) +
    cplxTruncForm d m_C c_C w_C (fun j => (u j).2)

/-- Alder–Strassen peeling lower bound for `cplxTruncForm` (`2 * (d - 1) * (c k - 1) + d` per
active nonreal rate). -/
lemma cplxTruncForm_rank_ge {ι_C : Type*} [Fintype ι_C] {d : ℕ} (hd : 2 ≤ d)
    (m_C : ι_C → ℕ) :
    ∀ (S : ℕ) (c : ι_C → ℕ), ∑ k, c k = S → (∀ k, c k ≤ m_C k) →
      ∀ (w : ι_C → ℕ → ℂ), (∀ k, 0 < c k → w k (c k - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → (CplxExpSpace m_C →ₗ[ℝ] ℝ)),
      (∀ u, cplxTruncForm d m_C c w u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d) ≤ R := by
  let := Classical.decEq ι_C
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro c hS hcm w hw R ℓ hrepr
    by_cases hall : ∀ k, c k = 0
    · simp [hall]
    push Not at hall
    obtain ⟨k₀, hk₀_ne⟩ := hall
    have hk₀_pos : 0 < c k₀ := Nat.pos_of_ne_zero hk₀_ne
    have hm₀_pos : 0 < m_C k₀ := lt_of_lt_of_le hk₀_pos (hcm k₀)
    have hd0 : 0 < d := by omega
    let j₀ : Fin d := ⟨0, hd0⟩
    let jLast : Fin d := ⟨d - 1, by omega⟩
    by_cases hc1 : c k₀ = 1
    · -- Case `c k₀ = 1`: peel `d` terms via `single_complex_rank_ge` and zero out block `k₀`.
      let q₀ : Fin (m_C k₀) := ⟨0, hm₀_pos⟩
      let emb0 := embCplxCoeff k₀ q₀
      let β₀ : ℂ := w k₀ 0
      have hβ₀ : β₀ ≠ 0 := by simpa [β₀, hc1] using hw k₀ hk₀_pos
      have hT_emb (z : Fin d → ℂ) :
          cplxTruncForm d m_C c w (fun j => emb0 (z j)) = (β₀ * ∏ j, z j).re := by
        simp only [cplxTruncForm]
        rw [Finset.sum_eq_single k₀]
        · rw [Finset.sum_eq_single (fun _ => q₀)]
          · simp [emb0, embCplxCoeff, β₀, q₀]
          · intro q _ hne
            have hex : ∃ j, q j ≠ q₀ := by
              by_contra h; push Not at h; exact hne (funext h)
            obtain ⟨j, hj⟩ := hex
            have h0 : emb0 (z j) k₀ (q j) = 0 :=
              singleCoeff_of_ne_deg k₀ q₀ (q j) (z j) hj
            rw [Finset.prod_eq_zero (Finset.mem_univ j) h0, mul_zero, Complex.zero_re]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [q₀, hc1]⟩) h
        · intro k _ hk
          refine Finset.sum_eq_zero fun q _ => ?_
          have h0 : emb0 (z j₀) k (q j₀) = 0 :=
            singleCoeff_of_ne_idx k₀ q₀ (z j₀) hk (q j₀)
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) h0, mul_zero, Complex.zero_re]
        · simp
      let killC : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        { toFun := fun x k => if k = k₀ then 0 else x k
          map_add' := fun a b => by ext k q; by_cases h : k = k₀ <;> simp [h]
          map_smul' := fun r a => by ext k q; by_cases h : k = k₀ <;> simp [h] }
      -- Mode `0`: find `2` distinct active terms `n₁ ≠ n₂`.
      have hex1 : ∃ n₁ : Fin R, ℓ n₁ j₀ (emb0 1) ≠ 0 := by
        by_contra h
        push Not at h
        let z (j : Fin d) : ℂ := if j = j₀ then 1 else if j = jLast then starRingEnd ℂ β₀ else 1
        have hz0 : z j₀ = 1 := by simp [z]
        have hprod_z : ∏ j : Fin d, z j = starRingEnd ℂ β₀ := by
          have hjL_ne : jLast ≠ j₀ := by
            intro he; have := congrArg Fin.val he; dsimp [jLast, j₀] at this; omega
          rw [← Finset.mul_prod_erase Finset.univ z (Finset.mem_univ jLast)]
          have her : ∏ j ∈ Finset.univ.erase jLast, z j = 1 :=
            Finset.prod_eq_one fun j hj => by
              have hne : j ≠ jLast := Finset.ne_of_mem_erase hj
              by_cases hj0 : j = j₀ <;> simp [z, hj0, hne]
          rw [her, mul_one]
          simp [z, hjL_ne]
        have hlhs := (hT_emb z).symm.trans (hrepr (fun j => emb0 (z j)))
        rw [hprod_z, Complex.mul_conj, Complex.ofReal_re] at hlhs
        have hrhs : ∑ n : Fin R, ∏ j : Fin d, ℓ n j (emb0 (z j)) = 0 :=
          Finset.sum_eq_zero fun n _ =>
            Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hz0]; exact h n)
        rw [hrhs] at hlhs
        exact (Complex.normSq_pos.mpr hβ₀).ne' hlhs
      obtain ⟨n₁, hn₁⟩ := hex1
      obtain ⟨w₁, hw₁_ne, hw₁_ker⟩ := exists_ker_ne_zero ((ℓ n₁ j₀).comp emb0)
      have hex2 : ∃ n₂ : Fin R, n₂ ≠ n₁ ∧ ℓ n₂ j₀ (emb0 w₁) ≠ 0 := by
        by_contra h
        push Not at h
        let z (j : Fin d) : ℂ :=
          if j = j₀ then w₁ else if j = jLast then starRingEnd ℂ (β₀ * w₁) else 1
        have hz0 : z j₀ = w₁ := by simp [z]
        have hjL_ne : jLast ≠ j₀ := by
          intro he; have := congrArg Fin.val he; dsimp [jLast, j₀] at this; omega
        have hprod_z : ∏ j : Fin d, z j = w₁ * starRingEnd ℂ (β₀ * w₁) := by
          rw [← Finset.mul_prod_erase Finset.univ z (Finset.mem_univ j₀),
            ← Finset.mul_prod_erase (Finset.univ.erase j₀) z
              (Finset.mem_erase.mpr ⟨hjL_ne, Finset.mem_univ jLast⟩)]
          have her : ∏ j ∈ (Finset.univ.erase j₀).erase jLast, z j = 1 :=
            Finset.prod_eq_one fun j hj => by
              have h1 : j ≠ jLast := (Finset.mem_erase.mp hj).1
              have h2 : j ≠ j₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
              simp [z, h1, h2]
          rw [her, mul_one]
          simp [z, hjL_ne]
        have hlhs := (hT_emb z).symm.trans (hrepr (fun j => emb0 (z j)))
        have hnorm : β₀ * (w₁ * starRingEnd ℂ (β₀ * w₁)) = Complex.normSq (β₀ * w₁) := by
          rw [← mul_assoc, Complex.mul_conj]
        rw [hprod_z, hnorm, Complex.ofReal_re] at hlhs
        have hrhs : ∑ n : Fin R, ∏ j : Fin d, ℓ n j (emb0 (z j)) = 0 :=
          Finset.sum_eq_zero fun n _ => by
            by_cases hn : n = n₁
            · subst hn
              exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hz0]; exact hw₁_ker)
            · exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hz0]; exact h n hn)
        rw [hrhs] at hlhs
        exact (Complex.normSq_pos.mpr (mul_ne_zero hβ₀ hw₁_ne)).ne' hlhs
      obtain ⟨n₂, hn₂₁, hn₂⟩ := hex2
      let c₁ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
        ((ℓ n₁ j₀ (emb0 1))⁻¹ • (ℓ n₁ j₀).comp killC).smulRight (1 : ℂ)
      let ψ₀a : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := killC - emb0.comp c₁
      have hψ₀a_kill1 (x : CplxExpSpace m_C) : ℓ n₁ j₀ (ψ₀a x) = 0 := by
        simp only [ψ₀a, c₁, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
        field_simp; ring
      let c₂ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
        ((ℓ n₂ j₀ (emb0 w₁))⁻¹ • (ℓ n₂ j₀).comp ψ₀a).smulRight w₁
      let ψ₀ : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := ψ₀a - emb0.comp c₂
      have hψ₀_kill1 (x : CplxExpSpace m_C) : ℓ n₁ j₀ (ψ₀ x) = 0 := by
        simp only [ψ₀, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smulRight_apply, map_sub, map_smul, hψ₀a_kill1 x]
        have hw10 : ℓ n₁ j₀ (emb0 w₁) = 0 := hw₁_ker
        simp [hw10]
      have hψ₀_kill2 (x : CplxExpSpace m_C) : ℓ n₂ j₀ (ψ₀ x) = 0 := by
        simp only [ψ₀, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
        field_simp; ring
      -- Modes `1, …, d - 2`: peel `1` more term per mode via `single_complex_rank_ge`.
      have hpeel : ∀ m ≤ d - 2,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C)),
          D.card = m + 2 ∧
          (∀ j : Fin d, (j : ℕ) < m + 1 →
            ∃ cj : CplxExpSpace m_C →ₗ[ℝ] ℂ, ∀ x, ψ j x = killC x - emb0 (cj x)) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < m + 1 ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro m hm
        induction m with
        | zero =>
          refine ⟨{n₁, n₂}, fun _ => ψ₀, Finset.card_pair hn₂₁.symm, ?_, ?_⟩
          · intro j hj
            have hj0 : j = j₀ := by ext; simp [j₀]; omega
            subst hj0
            refine ⟨c₁ + c₂, fun x => ?_⟩
            simp only [ψ₀, ψ₀a, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.add_apply, map_add]
            abel
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hn'
            · exact ⟨j₀, by simp [j₀], hψ₀_kill1⟩
            · rw [Finset.mem_singleton.mp hn']
              exact ⟨j₀, by simp [j₀], hψ₀_kill2⟩
        | succ m ihm =>
          obtain ⟨D, ψ, hDcard, hψ_form, hDkill⟩ := ihm (by omega)
          let jm : Fin d := ⟨m + 1, by omega⟩
          have hex_next : ∃ nr ∉ D, ∃ wr : ℂ, ℓ nr jm (emb0 wr) ≠ 0 := by
            by_contra hall
            push Not at hall
            let eD : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
            let ℓD (p : Fin D.card) (j : Fin d) : ℂ →ₗ[ℝ] ℝ := (ℓ (eD p).1 j).comp emb0
            have hD_repr (z : Fin d → ℂ) :
                (β₀ * ∏ j, z j).re = ∑ p : Fin D.card, ∏ j, ℓD p j (z j) := by
              rw [← hT_emb, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
              have hsdiff : ∑ n ∈ Finset.univ \ D, ∏ j, ℓ n j (emb0 (z j)) = 0 :=
                Finset.sum_eq_zero fun n hn =>
                  Finset.prod_eq_zero (Finset.mem_univ jm)
                    (hall n (Finset.mem_sdiff.mp hn).2 (z jm))
              rw [hsdiff, zero_add]
              change ∑ n ∈ D, ∏ j, ℓ n j (emb0 (z j)) = _
              rw [← Finset.sum_coe_sort D]
              exact (eD.sum_comp (fun x : D => ∏ j, ℓ x.1 j (emb0 (z j)))).symm
            have hge := single_complex_rank_ge hd hβ₀ ℓD hD_repr
            omega
          obtain ⟨nr, hnr_notD, wr, hwr⟩ := hex_next
          let cr : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
            ((ℓ nr jm (emb0 wr))⁻¹ • (ℓ nr jm).comp killC).smulRight wr
          let ψr : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := killC - emb0.comp cr
          have hψr_kill (x : CplxExpSpace m_C) : ℓ nr jm (ψr x) = 0 := by
            simp only [ψr, cr, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let ψ' (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
            if j = jm then ψr else ψ j
          refine ⟨insert nr D, ψ', Finset.card_insert_of_notMem hnr_notD ▸ by omega, ?_, ?_⟩
          · intro j hj
            by_cases hjm : j = jm
            · subst hjm; exact ⟨cr, fun x => by simp [ψ', ψr]⟩
            · have hlt : (j : ℕ) < m + 1 := by
                have hne : (j : ℕ) ≠ m + 1 := fun he => hjm (Fin.ext he)
                omega
              obtain ⟨cj, hcj⟩ := hψ_form j hlt
              exact ⟨cj, fun x => by simp [ψ', hjm, hcj]⟩
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hnD
            · exact ⟨jm, by simp [jm], fun x => by simp [ψ', hψr_kill]⟩
            · obtain ⟨j, hj, hkill⟩ := hDkill n hnD
              have hjm : j ≠ jm := by intro he; subst he; simp [jm] at hj
              exact ⟨j, by omega, fun x => by simp [ψ', hjm, hkill]⟩
      obtain ⟨D, ψ, hDcard, hψ_form, hDkill⟩ := hpeel (d - 2) (le_refl _)
      have hD_eq : D.card = d := by omega
      let φ (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        if (j : ℕ) < d - 1 then ψ j else killC
      let c' : ι_C → ℕ := Function.update c k₀ 0
      have hS' : ∑ k, c' k < S := by
        have h := sum_update_nat c k₀ 0
        change (∑ k, c' k) + c k₀ = (∑ k, c k) + 0 at h
        omega
      have hc'm : ∀ k, c' k ≤ m_C k := fun k => by
        by_cases hk : k = k₀ <;> simp [c', hk, hcm k]
      have hwc' : ∀ k, 0 < c' k → w k (c' k - 1) ≠ 0 := fun k hk => by
        by_cases hk0 : k = k₀
        · subst hk0; simp [c'] at hk
        · simp only [c', Function.update_of_ne hk0] at hk ⊢
          exact hw k hk
      have hT_red (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w u = cplxTruncForm d m_C c w (fun j => φ j (u j)) := by
        simp only [cplxTruncForm]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k₀),
          ← Finset.add_sum_erase Finset.univ
            (fun k => ∑ q ∈ Finset.univ.filter
                (fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c k),
              (w k (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k (q j)).re)
            (Finset.mem_univ k₀)]
        have hl0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_C k₀) => ∑ j, (q j : ℕ) < c' k₀),
            (w k₀ (∑ j, (q j : ℕ)) * ∏ j, u j k₀ (q j)).re = 0 := by simp [c']
        have hr0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_C k₀) => ∑ j, (q j : ℕ) < c k₀),
            (w k₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k₀ (q j)).re = 0 :=
          Finset.sum_eq_zero fun q _ => by
            have hjL : ¬ (jLast : ℕ) < d - 1 := by simp [jLast]
            have h0 : φ jLast (u jLast) k₀ (q jLast) = 0 := by simp [φ, hjL, killC]
            rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero, Complex.zero_re]
        rw [hl0, hr0, zero_add, zero_add]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk_ne : k ≠ k₀ := Finset.ne_of_mem_erase hk
        simp only [c', Function.update_of_ne hk_ne]
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 2
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : (j : ℕ) < d - 1
        · obtain ⟨cj, hcj⟩ := hψ_form j (by omega)
          simp [φ, hj, hcj, killC, hk_ne, emb0, embCplxCoeff,
            singleCoeff_of_ne_idx k₀ q₀ _ hk_ne]
        · simp [φ, hj, killC, hk_ne]
      let rem : Finset (Fin R) := Finset.univ \ D
      have hcard_rem : rem.card + D.card = R := by
        simpa [rem] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
        rw [hT_red, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
        have hD0 : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            obtain ⟨j, hj, hkill⟩ := hDkill n hn
            have hjd : (j : ℕ) < d - 1 := by omega
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            simp [φ, hjd, hkill]
        rw [hD0, add_zero]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hle := ih (∑ k, c' k) hS' c' rfl hc'm w hwc' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) + d =
          ∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else 2 * (d - 1) * (v - 1) + d) c k₀ 0
        change (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) +
            (if c k₀ = 0 then 0 else 2 * (d - 1) * (c k₀ - 1) + d) =
          (∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d) + 0 at h
        simp only [hc1, one_ne_zero, ↓reduceIte, Nat.sub_self, mul_zero, zero_add, add_zero] at h
        exact h
      omega
    · -- Case `c k₀ ≥ 2`: peel `2` terms in each mode `0, …, d - 2` (`2 * (d - 1)` total),
      -- then truncate low on `0, …, d - 2` and shift up on `d - 1`.
      have hc2 : 2 ≤ c k₀ := by omega
      let qTop : Fin (m_C k₀) := ⟨c k₀ - 1, lt_of_lt_of_le (by omega) (hcm k₀)⟩
      let q₀ : Fin (m_C k₀) := ⟨0, hm₀_pos⟩
      have hqTop_ne : qTop ≠ q₀ := by
        intro he; have := congrArg Fin.val he; dsimp [qTop, q₀] at this; omega
      let embTop := embCplxCoeff k₀ qTop
      let emb0 := embCplxCoeff k₀ q₀
      let βTop : ℂ := w k₀ (c k₀ - 1)
      have hβTop : βTop ≠ 0 := hw k₀ hk₀_pos
      have hpeel : ∀ r ≤ d - 1,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C)),
          D.card = 2 * r ∧
          (∀ j : Fin d, ¬ (j : ℕ) < r → ψ j = LinearMap.id) ∧
          (∀ j : Fin d, (j : ℕ) < r →
            ∃ cj : CplxExpSpace m_C →ₗ[ℝ] ℂ, ∀ x, ψ j x = x - embTop (cj x)) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < r ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro r hr
        induction r with
        | zero =>
          exact ⟨∅, fun _ => LinearMap.id, by simp, fun _ _ => rfl,
            fun _ hj => absurd hj (Nat.not_lt_zero _), by simp⟩
        | succ r ihr =>
          obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := ihr (by omega)
          let jr : Fin d := ⟨r, by omega⟩
          have hjr_ne_last : jr ≠ jLast := by
            intro he; have := congrArg Fin.val he; dsimp [jr, jLast] at this; omega
          let uOf (z : ℂ) (m : Fin d) : CplxExpSpace m_C :=
            if m = jr then embTop z
            else if m = jLast then emb0 (starRingEnd ℂ (βTop * z))
            else ψ m (emb0 1)
          have hTu (z : ℂ) :
              cplxTruncForm d m_C c w (uOf z) = Complex.normSq (βTop * z) := by
            simp only [cplxTruncForm]
            rw [Finset.sum_eq_single k₀]
            · let qTarget : Fin d → Fin (m_C k₀) := fun m => if m = jr then qTop else q₀
              have hqT_sum : ∑ m : Fin d, (qTarget m : ℕ) = c k₀ - 1 := by
                have hval (m : Fin d) : (qTarget m : ℕ) = if m = jr then c k₀ - 1 else 0 := by
                  by_cases hm : m = jr <;> simp [qTarget, hm, qTop, q₀]
                simp_rw [hval]
                simp
              rw [Finset.sum_eq_single qTarget]
              · rw [hqT_sum]
                have hprod_val : ∏ m : Fin d, uOf z m k₀ (qTarget m) =
                    z * starRingEnd ℂ (βTop * z) := by
                  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ jr),
                    ← Finset.mul_prod_erase (Finset.univ.erase jr) _
                      (Finset.mem_erase.mpr ⟨hjr_ne_last.symm, Finset.mem_univ jLast⟩)]
                  have her : ∏ m ∈ (Finset.univ.erase jr).erase jLast,
                      uOf z m k₀ (qTarget m) = 1 :=
                    Finset.prod_eq_one fun m hm => by
                      have hm_last : m ≠ jLast := (Finset.mem_erase.mp hm).1
                      have hm_jr : m ≠ jr := (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
                      by_cases hmr : (m : ℕ) < r
                      · obtain ⟨cm, hcm_eq⟩ := hψ_form m hmr
                        simp [uOf, hm_jr, hm_last, qTarget, hcm_eq, emb0, embTop, embCplxCoeff,
                          singleCoeff_of_ne_deg k₀ qTop q₀ _ hqTop_ne.symm]
                      · simp [uOf, hm_jr, hm_last, qTarget, hψ_id m hmr, emb0, embCplxCoeff]
                  rw [her, mul_one]
                  simp [uOf, hjr_ne_last.symm, qTarget, embTop, emb0, embCplxCoeff]
                rw [hprod_val]
                have hnorm : βTop * (z * starRingEnd ℂ (βTop * z)) = Complex.normSq (βTop * z) := by
                  rw [← mul_assoc, Complex.mul_conj]
                change (βTop * (z * starRingEnd ℂ (βTop * z))).re = _
                rw [hnorm, Complex.ofReal_re]
              · intro q hq hne
                have hqsum : ∑ m : Fin d, (q m : ℕ) < c k₀ := (Finset.mem_filter.mp hq).2
                by_cases hqjr : q jr = qTop
                · have hex : ∃ m ≠ jr, q m ≠ q₀ := by
                    by_contra h; push Not at h
                    refine hne (funext fun m => ?_)
                    by_cases hm : m = jr
                    · simp [qTarget, hm, hqjr]
                    · simp [qTarget, hm, h m hm]
                  obtain ⟨m, hm_ne, hqm_ne⟩ := hex
                  have hqm_zero : (q m : ℕ) = 0 := by
                    have hle : (q jr : ℕ) + (q m : ℕ) ≤ ∑ p : Fin d, (q p : ℕ) := by
                      rw [← Finset.add_sum_erase Finset.univ (fun p : Fin d => (q p : ℕ))
                        (Finset.mem_univ jr)]
                      exact Nat.add_le_add_left
                        (Finset.single_le_sum (f := fun p : Fin d => (q p : ℕ))
                          (fun _ _ => Nat.zero_le _)
                          (Finset.mem_erase.mpr ⟨hm_ne, Finset.mem_univ m⟩)) _
                    rw [hqjr] at hle; dsimp [qTop] at hle; omega
                  exact absurd (Fin.ext hqm_zero) hqm_ne
                · have hu0 : uOf z jr k₀ (q jr) = 0 := by
                    simp [uOf, embTop, embCplxCoeff, singleCoeff_of_ne_deg k₀ qTop (q jr) z hqjr]
                  rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero, Complex.zero_re]
              · intro h
                exact absurd (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, by rw [hqT_sum]; omega⟩) h
            · intro k _ hk
              refine Finset.sum_eq_zero fun q _ => ?_
              have hu0 : uOf z jr k (q jr) = 0 := by
                simp [uOf, embTop, embCplxCoeff, singleCoeff_of_ne_idx k₀ qTop z hk]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero, Complex.zero_re]
            · simp
          have hD_vanish (z : ℂ) (n : Fin R) (hn : n ∈ D) :
              ∏ m : Fin d, ℓ n m (uOf z m) = 0 := by
            obtain ⟨m, hm, hkill⟩ := hDkill n hn
            have hm_jr : m ≠ jr := by intro he; subst he; simp [jr] at hm
            have hm_last : m ≠ jLast := by
              intro he; subst he; dsimp [jLast] at hm; omega
            refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
            simp [uOf, hm_jr, hm_last, hkill]
          have hex1 : ∃ n₁ ∉ D, ℓ n₁ jr (embTop 1) ≠ 0 := by
            by_contra h; push Not at h
            have hlhs := (hTu 1).symm.trans (hrepr (uOf 1))
            rw [mul_one] at hlhs
            have hrhs : ∑ n : Fin R, ∏ m : Fin d, ℓ n m (uOf 1 m) = 0 :=
              Finset.sum_eq_zero fun n _ => by
                by_cases hnD : n ∈ D
                · exact hD_vanish 1 n hnD
                · refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                  simpa [uOf] using h n hnD
            rw [hrhs] at hlhs
            exact (Complex.normSq_pos.mpr hβTop).ne' hlhs
          obtain ⟨n₁, hn₁_notD, hn₁⟩ := hex1
          obtain ⟨w₁, hw₁_ne, hw₁_ker⟩ := exists_ker_ne_zero ((ℓ n₁ jr).comp embTop)
          have hex2 : ∃ n₂ ∉ insert n₁ D, ℓ n₂ jr (embTop w₁) ≠ 0 := by
            by_contra h; push Not at h
            have hlhs := (hTu w₁).symm.trans (hrepr (uOf w₁))
            have hrhs : ∑ n : Fin R, ∏ m : Fin d, ℓ n m (uOf w₁ m) = 0 :=
              Finset.sum_eq_zero fun n _ => by
                by_cases hn1 : n = n₁
                · subst hn1
                  refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                  simpa [uOf] using hw₁_ker
                · by_cases hnD : n ∈ D
                  · exact hD_vanish w₁ n hnD
                  · refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                    simpa [uOf] using h n (by simp [hn1, hnD])
            rw [hrhs] at hlhs
            exact (Complex.normSq_pos.mpr (mul_ne_zero hβTop hw₁_ne)).ne' hlhs
          obtain ⟨n₂, hn₂_not, hn₂⟩ := hex2
          let c₁ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
            ((ℓ n₁ jr (embTop 1))⁻¹ • ℓ n₁ jr).smulRight (1 : ℂ)
          let ψa : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
            LinearMap.id - embTop.comp c₁
          have hψa_kill1 (x : CplxExpSpace m_C) : ℓ n₁ jr (ψa x) = 0 := by
            simp only [ψa, c₁, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let c₂ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
            ((ℓ n₂ jr (embTop w₁))⁻¹ • (ℓ n₂ jr).comp ψa).smulRight w₁
          let ψb : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := ψa - embTop.comp c₂
          have hψb_kill1 (x : CplxExpSpace m_C) : ℓ n₁ jr (ψb x) = 0 := by
            simp only [ψb, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, map_sub, map_smul, hψa_kill1 x]
            have hw10 : ℓ n₁ jr (embTop w₁) = 0 := hw₁_ker
            simp [hw10]
          have hψb_kill2 (x : CplxExpSpace m_C) : ℓ n₂ jr (ψb x) = 0 := by
            simp only [ψb, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let ψ' (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
            if j = jr then ψb else ψ j
          have hcard_ins : (insert n₂ (insert n₁ D)).card = 2 * (r + 1) := by
            rw [Finset.card_insert_of_notMem hn₂_not, Finset.card_insert_of_notMem hn₁_notD,
              hDcard]
            omega
          refine ⟨insert n₂ (insert n₁ D), ψ', hcard_ins, ?_, ?_, ?_⟩
          · intro j hj
            have hj_ne : j ≠ jr := by intro he; subst he; simp [jr] at hj
            simp [ψ', hj_ne, hψ_id j (by omega)]
          · intro j hj
            by_cases hjr : j = jr
            · subst hjr
              refine ⟨c₁ + c₂, fun x => ?_⟩
              simp only [ψ', ↓reduceIte, ψb, ψa, LinearMap.sub_apply, LinearMap.id_apply,
                LinearMap.comp_apply, LinearMap.add_apply, map_add]
              abel
            · have hlt : (j : ℕ) < r := by
                have hne : (j : ℕ) ≠ r := fun he => hjr (Fin.ext he)
                omega
              obtain ⟨cj, hcj⟩ := hψ_form j hlt
              exact ⟨cj, fun x => by simp [ψ', hjr, hcj]⟩
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hn'
            · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψb_kill2]⟩
            · rcases Finset.mem_insert.mp hn' with rfl | hnD
              · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψb_kill1]⟩
              · obtain ⟨j, hj, hkill⟩ := hDkill n hnD
                have hjr : j ≠ jr := by intro he; subst he; simp [jr] at hj
                exact ⟨j, by omega, fun x => by simp [ψ', hjr, hkill]⟩
      obtain ⟨D, ψ, hDcard, _, hψ_form, hDkill⟩ := hpeel (d - 1) (le_refl _)
      let truncLow : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        { toFun := fun x k q =>
            if k = k₀ then if (q : ℕ) + 1 < c k₀ then x k q else 0 else x k q
          map_add' := fun a b => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : (q : ℕ) + 1 < c k₀ <;> simp [hk, hq]
            · simp [hk]
          map_smul' := fun r a => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : (q : ℕ) + 1 < c k₀ <;> simp [hk, hq]
            · simp [hk] }
      let shiftUp : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        { toFun := fun x k q =>
            if k = k₀ then
              if hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c k₀ then
                x k₀ ⟨(q : ℕ) - 1, by have := hcm k₀; omega⟩
              else 0
            else x k q
          map_add' := fun a b => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c k₀ <;> simp [hk, hq]
            · simp [hk]
          map_smul' := fun r a => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c k₀ <;> simp [hk, hq]
            · simp [hk] }
      let φ (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        if j = jLast then shiftUp else (ψ j).comp truncLow
      let c' : ι_C → ℕ := Function.update c k₀ (c k₀ - 1)
      let w' : ι_C → ℕ → ℂ := Function.update w k₀ (fun m => w k₀ (m + 1))
      have hS' : ∑ k, c' k < S := by
        have h := sum_update_nat c k₀ (c k₀ - 1)
        change (∑ k, c' k) + c k₀ = (∑ k, c k) + (c k₀ - 1) at h
        omega
      have hc'm : ∀ k, c' k ≤ m_C k := fun k => by
        by_cases hk : k = k₀
        · rw [hk]; simp only [c', Function.update_self]; have := hcm k₀; omega
        · simp [c', hk, hcm k]
      have hwc' : ∀ k, 0 < c' k → w' k (c' k - 1) ≠ 0 := fun k hk => by
        by_cases hk0 : k = k₀
        · subst hk0
          simp only [c', w', Function.update_self] at hk ⊢
          have : c k - 1 - 1 + 1 = c k - 1 := by omega
          rw [this]; exact hw k hk₀_pos
        · simp only [c', w', Function.update_of_ne hk0] at hk ⊢
          exact hw k hk
      have hφ_other (j : Fin d) (k : ι_C) (hk : k ≠ k₀) (x : CplxExpSpace m_C) (q : Fin (m_C k)) :
          φ j x k q = x k q := by
        by_cases hj : j = jLast
        · simp [φ, hj, shiftUp, hk]
        · have hjlt : (j : ℕ) < d - 1 := by
            have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
            omega
          obtain ⟨cj, hcj⟩ := hψ_form j hjlt
          simp [φ, hj, hcj, truncLow, hk, embTop, embCplxCoeff,
            singleCoeff_of_ne_idx k₀ qTop _ hk]
      have hφ_low (j : Fin d) (hj : j ≠ jLast) (x : CplxExpSpace m_C) (q : Fin (m_C k₀))
          (hq : (q : ℕ) + 1 < c k₀) :
          φ j x k₀ q = x k₀ q := by
        have hjlt : (j : ℕ) < d - 1 := by
          have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
          omega
        obtain ⟨cj, hcj⟩ := hψ_form j hjlt
        have hq_ne : q ≠ qTop := by
          intro he; have := congrArg Fin.val he; dsimp [qTop] at this; omega
        simp [φ, hj, hcj, truncLow, hq, embTop, embCplxCoeff,
          singleCoeff_of_ne_deg k₀ qTop q _ hq_ne]
      have hT_red (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w' u = cplxTruncForm d m_C c w (fun j => φ j (u j)) := by
        simp only [cplxTruncForm]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = k₀
        · subst hk
          simp only [c', w', Function.update_self]
          have hsplit := (Finset.sum_filter_add_sum_filter_not
            (Finset.univ.filter fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c k)
            (fun q : Fin d → Fin (m_C k) => 1 ≤ (q jLast : ℕ))
            (fun q => (w k (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k (q j)).re)).symm
          have hzero_part :
              ∑ q ∈ (Finset.univ.filter fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c k).filter
                (fun q => ¬ 1 ≤ (q jLast : ℕ)),
                (w k (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k (q j)).re = 0 :=
            Finset.sum_eq_zero fun q hq => by
              have hnot1 : ¬ 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have h0 : φ jLast (u jLast) k (q jLast) = 0 := by simp [φ, shiftUp, hnot1]
              rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero, Complex.zero_re]
          rw [hsplit, hzero_part, add_zero]
          let toHi (q' : Fin d → Fin (m_C k)) (j : Fin d) : Fin (m_C k) :=
            if j = jLast then
              if h : (q' jLast : ℕ) + 1 < m_C k then ⟨(q' jLast : ℕ) + 1, h⟩ else q' jLast
            else q' j
          let toLow (q : Fin d → Fin (m_C k)) (j : Fin d) : Fin (m_C k) :=
            if j = jLast then ⟨(q jLast : ℕ) - 1, by omega⟩ else q j
          have htoHi (q' : Fin d → Fin (m_C k)) (hq' : ∑ j, (q' j : ℕ) < c k - 1) :
              (q' jLast : ℕ) + 1 < m_C k ∧
                ∑ j, (toHi q' j : ℕ) = (∑ j, (q' j : ℕ)) + 1 := by
            have hlast_lt : (q' jLast : ℕ) + 1 < m_C k := by
              have hle := Finset.single_le_sum (f := fun j : Fin d => (q' j : ℕ))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
              have := hcm k; omega
            refine ⟨hlast_lt, ?_⟩
            have h := sum_update_nat (fun j => (q' j : ℕ)) jLast ((q' jLast : ℕ) + 1)
            have heq : ∑ j, (toHi q' j : ℕ) =
                ∑ j, Function.update (fun m => (q' m : ℕ)) jLast ((q' jLast : ℕ) + 1) j :=
              Finset.sum_congr rfl fun j _ => by
                by_cases hj : j = jLast <;> simp [toHi, hj, hlast_lt]
            rw [heq]; omega
          refine Finset.sum_nbij' toHi toLow ?_ ?_ ?_ ?_ ?_
          · intro q' hq'
            obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' (Finset.mem_filter.mp hq').2
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [hsum_hi]; have := (Finset.mem_filter.mp hq').2; omega
            · simp [toHi, hlast_lt]
          · intro q hq
            have hq_sum : ∑ j, (q j : ℕ) < c k :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
            have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
            have h := sum_update_nat (fun j => (q j : ℕ)) jLast ((q jLast : ℕ) - 1)
            have heq : ∑ j, (toLow q j : ℕ) =
                ∑ j, Function.update (fun m => (q m : ℕ)) jLast ((q jLast : ℕ) - 1) j :=
              Finset.sum_congr rfl fun j _ => by
                by_cases hj : j = jLast <;> simp [toLow, hj]
            rw [← heq] at h
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          · intro q' hq'
            obtain ⟨hlast_lt, _⟩ := htoHi q' (Finset.mem_filter.mp hq').2
            ext j
            by_cases hj : j = jLast <;> simp [toLow, toHi, hj, hlast_lt]
          · intro q hq
            have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
            have hlt_m : (q jLast : ℕ) - 1 + 1 < m_C k := by
              have := (q jLast).2; omega
            ext j
            by_cases hj : j = jLast
            · subst hj; simp [toHi, toLow, hlt_m]; omega
            · simp [toHi, toLow, hj]
          · intro q' hq'
            have hq'_lt : ∑ j, (q' j : ℕ) < c k - 1 := (Finset.mem_filter.mp hq').2
            obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' hq'_lt
            rw [hsum_hi]
            congr 2
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = jLast
            · subst hj
              have hcond : 1 ≤ (q' jLast : ℕ) + 1 ∧ (q' jLast : ℕ) + 1 < c k := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                omega
              simp [toHi, hlast_lt, φ, shiftUp, hcond]
            · simp only [toHi, hj, ↓reduceIte]
              have hqj_lt : (q' j : ℕ) + 1 < c k := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                omega
              exact (hφ_low j hj (u j) (q' j) hqj_lt).symm
        · simp only [c', w', Function.update_of_ne hk]
          refine Finset.sum_congr rfl fun q _ => ?_
          congr 2
          exact Finset.prod_congr rfl fun j _ => (hφ_other j k hk (u j) (q j)).symm
      let rem : Finset (Fin R) := Finset.univ \ D
      have hcard_rem : rem.card + D.card = R := by
        simpa [rem] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w' u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
        rw [hT_red, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
        have hD0 : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            obtain ⟨j, hj, hkill⟩ := hDkill n hn
            have hj_ne : j ≠ jLast := by
              intro he; subst he; simp [jLast] at hj
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            simp [φ, hj_ne, hkill]
        rw [hD0, add_zero]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hle := ih (∑ k, c' k) hS' c' rfl hc'm w' hwc' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) + 2 * (d - 1) =
          ∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else 2 * (d - 1) * (v - 1) + d) c k₀ (c k₀ - 1)
        change (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) +
            (if c k₀ = 0 then 0 else 2 * (d - 1) * (c k₀ - 1) + d) =
          (∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d) +
            (if c k₀ - 1 = 0 then 0 else 2 * (d - 1) * (c k₀ - 1 - 1) + d) at h
        have h1 : c k₀ ≠ 0 := hk₀_ne
        have h2 : c k₀ - 1 ≠ 0 := by omega
        simp only [h1, h2, ↓reduceIte] at h
        have hmul : 2 * (d - 1) * (c k₀ - 1) =
            2 * (d - 1) * (c k₀ - 1 - 1) + 2 * (d - 1) := by
          have hsub : c k₀ - 1 = (c k₀ - 1 - 1) + 1 := by omega
          conv_lhs => rw [hsub, mul_add, mul_one]
        omega
      omega

/-- Alder–Strassen peeling lower bound for `realExpForm` across both real and nonreal rates of
arbitrary polynomial degrees. -/
lemma realExpForm_rank_ge {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C] {d : ℕ} (hd : 2 ≤ d)
    (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_C : ι_C → ℕ) (hcC : ∀ k, c_C k ≤ m_C k)
    (w_C : ι_C → ℕ → ℂ) (hwC : ∀ k, 0 < c_C k → w_C k (c_C k - 1) ≠ 0) :
    ∀ (S : ℕ) (c_R : ι_R → ℕ), ∑ i, c_R i = S → (∀ i, c_R i ≤ m_R i) →
      ∀ (w_R : ι_R → ℕ → ℝ), (∀ i, 0 < c_R i → w_R i (c_R i - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → (RealExpSpace m_R m_C →ₗ[ℝ] ℝ)),
      (∀ u, realExpForm d m_R m_C c_R c_C w_R w_C u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1) +
        (∑ k, if c_C k = 0 then 0 else 2 * (d - 1) * (c_C k - 1) + d) ≤ R := by
  let := Classical.decEq ι_R
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro c_R hS hcRm w_R hwR R ℓ hrepr
    by_cases hall : ∀ i, c_R i = 0
    · simp only [hall, ↓reduceIte, Finset.sum_const_zero, zero_add]
      let inrC : CplxExpSpace m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        LinearMap.inr ℝ (∀ i, Fin (m_R i) → ℝ) (CplxExpSpace m_C)
      let ℓC (n : Fin R) (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] ℝ := (ℓ n j).comp inrC
      have hreprC (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c_C w_C u = ∑ n, ∏ j, ℓC n j (u j) := by
        have h := hrepr (fun j => (0, u j))
        have hr0 : realTruncForm d m_R c_R w_R (fun _ => 0) = 0 := by
          simp [realTruncForm, hall]
        simp only [realExpForm, hr0, zero_add] at h
        exact h
      exact cplxTruncForm_rank_ge hd m_C (∑ k, c_C k) c_C rfl hcC w_C hwC R ℓC hreprC
    push Not at hall
    obtain ⟨i₀, hi₀_ne⟩ := hall
    have hi₀_pos : 0 < c_R i₀ := Nat.pos_of_ne_zero hi₀_ne
    have hm₀_pos : 0 < m_R i₀ := lt_of_lt_of_le hi₀_pos (hcRm i₀)
    have hd0 : 0 < d := by omega
    let j₀ : Fin d := ⟨0, hd0⟩
    let jLast : Fin d := ⟨d - 1, by omega⟩
    by_cases hc1 : c_R i₀ = 1
    · -- Case `c_R i₀ = 1`: kill `1` term on mode `0` and zero block `i₀` on modes `j ≥ 1`.
      let q₀ : Fin (m_R i₀) := ⟨0, hm₀_pos⟩
      let e₀ : RealExpSpace m_R m_C := embRealCoeff i₀ q₀ 1
      have hTe : realExpForm d m_R m_C c_R c_C w_R w_C (fun _ => e₀) = w_R i₀ 0 := by
        have hc0 : cplxTruncForm d m_C c_C w_C (fun _ => e₀.2) = 0 := by
          refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun q _ => ?_
          have h0 : e₀.2 k (q j₀) = 0 := rfl
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) h0, mul_zero, Complex.zero_re]
        simp only [realExpForm, hc0, add_zero, realTruncForm]
        rw [Finset.sum_eq_single i₀]
        · rw [Finset.sum_eq_single (fun _ => q₀)]
          · simp [e₀, embRealCoeff, q₀]
          · intro q _ hne
            have hex : ∃ j, q j ≠ q₀ := by
              by_contra h; push Not at h; exact hne (funext h)
            obtain ⟨j, hj⟩ := hex
            have h0 : e₀.1 i₀ (q j) = 0 := singleRealCoeff_of_ne_deg i₀ q₀ (q j) 1 hj
            rw [Finset.prod_eq_zero (Finset.mem_univ j) h0, mul_zero]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [q₀, hc1]⟩) h
        · intro i _ hi
          refine Finset.sum_eq_zero fun q _ => ?_
          have h0 : e₀.1 i (q j₀) = 0 := singleRealCoeff_of_ne_idx i₀ q₀ 1 hi (q j₀)
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) h0, mul_zero]
        · simp
      have hw0 : w_R i₀ 0 ≠ 0 := by simpa [hc1] using hwR i₀ hi₀_pos
      have hsum_ne : ∑ n : Fin R, ∏ j : Fin d, ℓ n j e₀ ≠ 0 := by
        rw [← hrepr]; exact hTe ▸ hw0
      obtain ⟨n₀, _, hn₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
      have hℓ0 : ℓ n₀ j₀ e₀ ≠ 0 := fun h =>
        hn₀ (Finset.prod_eq_zero (Finset.mem_univ j₀) h)
      let killR : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        { toFun := fun x => (fun i => if i = i₀ then 0 else x.1 i, x.2)
          map_add' := fun a b => by
            ext i q
            · by_cases hi : i = i₀ <;> simp [hi]
            · rfl
          map_smul' := fun r a => by
            ext i q
            · by_cases hi : i = i₀ <;> simp [hi]
            · rfl }
      let φ₀ : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        killR - ((ℓ n₀ j₀ e₀)⁻¹ • (ℓ n₀ j₀).comp killR).smulRight e₀
      have hφ₀_kill (x : RealExpSpace m_R m_C) : ℓ n₀ j₀ (φ₀ x) = 0 := by
        simp only [φ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
        field_simp; ring
      let φ (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        if j = j₀ then φ₀ else killR
      let c_R' : ι_R → ℕ := Function.update c_R i₀ 0
      have hS' : ∑ i, c_R' i < S := by
        have h := sum_update_nat c_R i₀ 0
        change (∑ i, c_R' i) + c_R i₀ = (∑ i, c_R i) + 0 at h
        omega
      have hcR'm : ∀ i, c_R' i ≤ m_R i := fun i => by
        by_cases hi : i = i₀ <;> simp [c_R', hi, hcRm i]
      have hwR' : ∀ i, 0 < c_R' i → w_R i (c_R' i - 1) ≠ 0 := fun i hi => by
        by_cases hi0 : i = i₀
        · subst hi0; simp [c_R'] at hi
        · simp only [c_R', Function.update_of_ne hi0] at hi ⊢
          exact hwR i hi
      have hφ_snd (j : Fin d) (x : RealExpSpace m_R m_C) : (φ j x).2 = x.2 := by
        by_cases hj : j = j₀ <;> simp [φ, hj, φ₀, killR, e₀, embRealCoeff]
      have hT_red (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R w_C u =
            realExpForm d m_R m_C c_R c_C w_R w_C (fun j => φ j (u j)) := by
        simp only [realExpForm, hφ_snd]
        congr 1
        simp only [realTruncForm]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase Finset.univ
            (fun i => ∑ q ∈ Finset.univ.filter
                (fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i),
              w_R i (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i (q j))
            (Finset.mem_univ i₀)]
        have hl0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_R i₀) => ∑ j, (q j : ℕ) < c_R' i₀),
            w_R i₀ (∑ j, (q j : ℕ)) * ∏ j, (u j).1 i₀ (q j) = 0 := by simp [c_R']
        have hr0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_R i₀) => ∑ j, (q j : ℕ) < c_R i₀),
            w_R i₀ (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i₀ (q j) = 0 :=
          Finset.sum_eq_zero fun q _ => by
            have hjL_ne : jLast ≠ j₀ := by
              intro he; have := congrArg Fin.val he; dsimp [jLast, j₀] at this; omega
            have h0 : (φ jLast (u jLast)).1 i₀ (q jLast) = 0 := by
              simp [φ, hjL_ne, killR]
            rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero]
        rw [hl0, hr0, zero_add, zero_add]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_ne : i ≠ i₀ := Finset.ne_of_mem_erase hi
        simp only [c_R', Function.update_of_ne hi_ne]
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = j₀
        · simp [φ, hj, φ₀, killR, hi_ne, e₀, embRealCoeff,
            singleRealCoeff_of_ne_idx i₀ q₀ 1 hi_ne]
        · simp [φ, hj, killR, hi_ne]
      let rem : Finset (Fin R) := Finset.univ.erase n₀
      have hcard_rem : rem.card + 1 = R := by
        simpa [rem] using Finset.card_erase_add_one (Finset.mem_univ n₀)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R w_C u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
        rw [hT_red, hrepr, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ n₀)]
        have hn0_zero : ∏ j : Fin d, ℓ n₀ j (φ j (u j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [φ, hφ₀_kill])
        rw [hn0_zero, zero_add]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hle := ih (∑ i, c_R' i) hS' c_R' rfl hcR'm w_R hwR' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) + 1 =
          ∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1 := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else (d - 1) * (v - 1) + 1) c_R i₀ 0
        change (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) +
            (if c_R i₀ = 0 then 0 else (d - 1) * (c_R i₀ - 1) + 1) =
          (∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1) + 0 at h
        simp only [hc1, one_ne_zero, ↓reduceIte, Nat.sub_self, mul_zero, zero_add, add_zero] at h
        exact h
      omega
    · -- Case `c_R i₀ ≥ 2`: peel `d - 1` terms on modes `0, …, d - 2` along `sTop`, then shift up.
      have hc2 : 2 ≤ c_R i₀ := by omega
      let qTop : Fin (m_R i₀) := ⟨c_R i₀ - 1, lt_of_lt_of_le (by omega) (hcRm i₀)⟩
      let q₀ : Fin (m_R i₀) := ⟨0, hm₀_pos⟩
      have hqTop_ne : qTop ≠ q₀ := by
        intro he; have := congrArg Fin.val he; dsimp [qTop, q₀] at this; omega
      let sTop : RealExpSpace m_R m_C := embRealCoeff i₀ qTop 1
      let s₀ : RealExpSpace m_R m_C := embRealCoeff i₀ q₀ 1
      have hpeel : ∀ r ≤ d - 1,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C)),
          D.card = r ∧
          (∀ j : Fin d, ¬ (j : ℕ) < r → ψ j = LinearMap.id) ∧
          (∀ j : Fin d, (j : ℕ) < r →
            ∃ cj : RealExpSpace m_R m_C →ₗ[ℝ] ℝ, ∀ x, ψ j x = x - cj x • sTop) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < r ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro r hr
        induction r with
        | zero =>
          exact ⟨∅, fun _ => LinearMap.id, by simp, fun _ _ => rfl,
            fun _ hj => absurd hj (Nat.not_lt_zero _), by simp⟩
        | succ r ihr =>
          obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := ihr (by omega)
          let jr : Fin d := ⟨r, by omega⟩
          let u (m : Fin d) : RealExpSpace m_R m_C := if m = jr then sTop else ψ m s₀
          have hTu : realExpForm d m_R m_C c_R c_C w_R w_C u = w_R i₀ (c_R i₀ - 1) := by
            have hc0 : cplxTruncForm d m_C c_C w_C (fun j => (u j).2) = 0 := by
              refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun q _ => ?_
              have h0 : (u jr).2 k (q jr) = 0 := by simp [u, sTop, embRealCoeff]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) h0, mul_zero, Complex.zero_re]
            simp only [realExpForm, hc0, add_zero, realTruncForm]
            rw [Finset.sum_eq_single i₀]
            · let qTarget : Fin d → Fin (m_R i₀) := fun m => if m = jr then qTop else q₀
              have hqT_sum : ∑ m : Fin d, (qTarget m : ℕ) = c_R i₀ - 1 := by
                have hval (m : Fin d) : (qTarget m : ℕ) = if m = jr then c_R i₀ - 1 else 0 := by
                  by_cases hm : m = jr <;> simp [qTarget, hm, qTop, q₀]
                simp_rw [hval]; simp
              rw [Finset.sum_eq_single qTarget]
              · rw [hqT_sum]
                suffices ∏ m : Fin d, (u m).1 i₀ (qTarget m) = 1 by rw [this, mul_one]
                refine Finset.prod_eq_one fun m _ => ?_
                by_cases hm : m = jr
                · subst hm; simp [u, qTarget, sTop, embRealCoeff]
                · by_cases hmr : (m : ℕ) < r
                  · obtain ⟨cm, hcm_eq⟩ := hψ_form m hmr
                    simp [u, hm, qTarget, hcm_eq, s₀, sTop, embRealCoeff,
                      singleRealCoeff_of_ne_deg i₀ qTop q₀ 1 hqTop_ne.symm]
                  · simp [u, hm, qTarget, hψ_id m hmr, s₀, embRealCoeff]
              · intro q hq hne
                have hqsum : ∑ m : Fin d, (q m : ℕ) < c_R i₀ := (Finset.mem_filter.mp hq).2
                by_cases hqjr : q jr = qTop
                · have hex : ∃ m ≠ jr, q m ≠ q₀ := by
                    by_contra h; push Not at h
                    refine hne (funext fun m => ?_)
                    by_cases hm : m = jr
                    · simp [qTarget, hm, hqjr]
                    · simp [qTarget, hm, h m hm]
                  obtain ⟨m, hm_ne, hqm_ne⟩ := hex
                  have hqm_zero : (q m : ℕ) = 0 := by
                    have hle : (q jr : ℕ) + (q m : ℕ) ≤ ∑ p : Fin d, (q p : ℕ) := by
                      rw [← Finset.add_sum_erase Finset.univ (fun p : Fin d => (q p : ℕ))
                        (Finset.mem_univ jr)]
                      exact Nat.add_le_add_left
                        (Finset.single_le_sum (f := fun p : Fin d => (q p : ℕ))
                          (fun _ _ => Nat.zero_le _)
                          (Finset.mem_erase.mpr ⟨hm_ne, Finset.mem_univ m⟩)) _
                    rw [hqjr] at hle; dsimp [qTop] at hle; omega
                  exact absurd (Fin.ext hqm_zero) hqm_ne
                · have hu0 : (u jr).1 i₀ (q jr) = 0 := by
                    simp [u, sTop, embRealCoeff,
                      singleRealCoeff_of_ne_deg i₀ qTop (q jr) 1 hqjr]
                  rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
              · intro h
                exact absurd (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, by rw [hqT_sum]; omega⟩) h
            · intro i _ hi
              refine Finset.sum_eq_zero fun q _ => ?_
              have hu0 : (u jr).1 i (q jr) = 0 := by
                simp [u, sTop, embRealCoeff, singleRealCoeff_of_ne_idx i₀ qTop 1 hi]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
            · simp
          have htop_ne : w_R i₀ (c_R i₀ - 1) ≠ 0 := hwR i₀ hi₀_pos
          have hex : ∃ nr ∉ D, ℓ nr jr sTop ≠ 0 := by
            by_contra hall; push Not at hall
            have hlhs := hTu.symm.trans (hrepr u)
            have hrhs : ∑ n : Fin R, ∏ m : Fin d, ℓ n m (u m) = 0 :=
              Finset.sum_eq_zero fun n _ => by
                by_cases hnD : n ∈ D
                · obtain ⟨m, hm, hkill⟩ := hDkill n hnD
                  have hm_ne : m ≠ jr := by intro he; subst he; simp [jr] at hm
                  refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
                  simp [u, hm_ne, hkill]
                · refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                  simpa [u] using hall n hnD
            rw [hrhs] at hlhs
            exact htop_ne hlhs
          obtain ⟨nr, hnr_notD, hnr⟩ := hex
          let cr : RealExpSpace m_R m_C →ₗ[ℝ] ℝ := (ℓ nr jr sTop)⁻¹ • ℓ nr jr
          let ψr : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
            LinearMap.id - cr.smulRight sTop
          have hψr_kill (x : RealExpSpace m_R m_C) : ℓ nr jr (ψr x) = 0 := by
            simp only [ψr, cr, LinearMap.sub_apply, LinearMap.id_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let ψ' (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
            if j = jr then ψr else ψ j
          refine ⟨insert nr D, ψ', Finset.card_insert_of_notMem hnr_notD ▸ by omega, ?_, ?_, ?_⟩
          · intro j hj
            have hj_ne : j ≠ jr := by intro he; subst he; simp [jr] at hj
            simp [ψ', hj_ne, hψ_id j (by omega)]
          · intro j hj
            by_cases hjr : j = jr
            · subst hjr; exact ⟨cr, fun x => by simp [ψ', ψr]⟩
            · have hlt : (j : ℕ) < r := by
                have hne : (j : ℕ) ≠ r := fun he => hjr (Fin.ext he)
                omega
              obtain ⟨cj, hcj⟩ := hψ_form j hlt
              exact ⟨cj, fun x => by simp [ψ', hjr, hcj]⟩
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hnD
            · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψr_kill]⟩
            · obtain ⟨j, hj, hkill⟩ := hDkill n hnD
              have hjr : j ≠ jr := by intro he; subst he; simp [jr] at hj
              exact ⟨j, by omega, fun x => by simp [ψ', hjr, hkill]⟩
      obtain ⟨D, ψ, hDcard, _, hψ_form, hDkill⟩ := hpeel (d - 1) (le_refl _)
      let truncLow : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        { toFun := fun x =>
            (fun i q => if i = i₀ then if (q : ℕ) + 1 < c_R i₀ then x.1 i q else 0 else x.1 i q,
             x.2)
          map_add' := fun a b => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : (q : ℕ) + 1 < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl
          map_smul' := fun r a => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : (q : ℕ) + 1 < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl }
      let shiftUp : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        { toFun := fun x =>
            (fun i q =>
              if i = i₀ then
                if hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c_R i₀ then
                  x.1 i₀ ⟨(q : ℕ) - 1, by have := hcRm i₀; omega⟩
                else 0
              else x.1 i q,
             x.2)
          map_add' := fun a b => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl
          map_smul' := fun r a => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl }
      let φ (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        if j = jLast then shiftUp else (ψ j).comp truncLow
      let c_R' : ι_R → ℕ := Function.update c_R i₀ (c_R i₀ - 1)
      let w_R' : ι_R → ℕ → ℝ := Function.update w_R i₀ (fun m => w_R i₀ (m + 1))
      have hS' : ∑ i, c_R' i < S := by
        have h := sum_update_nat c_R i₀ (c_R i₀ - 1)
        change (∑ i, c_R' i) + c_R i₀ = (∑ i, c_R i) + (c_R i₀ - 1) at h
        omega
      have hcR'm : ∀ i, c_R' i ≤ m_R i := fun i => by
        by_cases hi : i = i₀
        · rw [hi]; simp only [c_R', Function.update_self]; have := hcRm i₀; omega
        · simp [c_R', hi, hcRm i]
      have hwR' : ∀ i, 0 < c_R' i → w_R' i (c_R' i - 1) ≠ 0 := fun i hi => by
        by_cases hi0 : i = i₀
        · subst hi0
          simp only [c_R', w_R', Function.update_self] at hi ⊢
          have : c_R i - 1 - 1 + 1 = c_R i - 1 := by omega
          rw [this]; exact hwR i hi₀_pos
        · simp only [c_R', w_R', Function.update_of_ne hi0] at hi ⊢
          exact hwR i hi
      have hφ_snd (j : Fin d) (x : RealExpSpace m_R m_C) : (φ j x).2 = x.2 := by
        by_cases hj : j = jLast
        · simp [φ, hj, shiftUp]
        · have hjlt : (j : ℕ) < d - 1 := by
            have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
            omega
          obtain ⟨cj, hcj⟩ := hψ_form j hjlt
          simp [φ, hj, hcj, truncLow, sTop, embRealCoeff]
      have hφ_other (j : Fin d) (i : ι_R) (hi : i ≠ i₀) (x : RealExpSpace m_R m_C)
          (q : Fin (m_R i)) :
          (φ j x).1 i q = x.1 i q := by
        by_cases hj : j = jLast
        · simp [φ, hj, shiftUp, hi]
        · have hjlt : (j : ℕ) < d - 1 := by
            have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
            omega
          obtain ⟨cj, hcj⟩ := hψ_form j hjlt
          simp [φ, hj, hcj, truncLow, hi, sTop, embRealCoeff,
            singleRealCoeff_of_ne_idx i₀ qTop 1 hi]
      have hφ_low (j : Fin d) (hj : j ≠ jLast) (x : RealExpSpace m_R m_C) (q : Fin (m_R i₀))
          (hq : (q : ℕ) + 1 < c_R i₀) :
          (φ j x).1 i₀ q = x.1 i₀ q := by
        have hjlt : (j : ℕ) < d - 1 := by
          have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
          omega
        obtain ⟨cj, hcj⟩ := hψ_form j hjlt
        have hq_ne : q ≠ qTop := by
          intro he; have := congrArg Fin.val he; dsimp [qTop] at this; omega
        simp [φ, hj, hcj, truncLow, hq, sTop, embRealCoeff,
          singleRealCoeff_of_ne_deg i₀ qTop q 1 hq_ne]
      have hT_red (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R' w_C u =
            realExpForm d m_R m_C c_R c_C w_R w_C (fun j => φ j (u j)) := by
        simp only [realExpForm, hφ_snd]
        congr 1
        simp only [realTruncForm]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i = i₀
        · subst hi
          simp only [c_R', w_R', Function.update_self]
          have hsplit := (Finset.sum_filter_add_sum_filter_not
            (Finset.univ.filter fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i)
            (fun q : Fin d → Fin (m_R i) => 1 ≤ (q jLast : ℕ))
            (fun q => w_R i (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i (q j))).symm
          have hzero_part :
              ∑ q ∈ (Finset.univ.filter
                  fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i).filter
                (fun q => ¬ 1 ≤ (q jLast : ℕ)),
                w_R i (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i (q j) = 0 :=
            Finset.sum_eq_zero fun q hq => by
              have hnot1 : ¬ 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have h0 : (φ jLast (u jLast)).1 i (q jLast) = 0 := by simp [φ, shiftUp, hnot1]
              rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero]
          rw [hsplit, hzero_part, add_zero]
          let toHi (q' : Fin d → Fin (m_R i)) (j : Fin d) : Fin (m_R i) :=
            if j = jLast then
              if h : (q' jLast : ℕ) + 1 < m_R i then ⟨(q' jLast : ℕ) + 1, h⟩ else q' jLast
            else q' j
          let toLow (q : Fin d → Fin (m_R i)) (j : Fin d) : Fin (m_R i) :=
            if j = jLast then ⟨(q jLast : ℕ) - 1, by omega⟩ else q j
          have htoHi (q' : Fin d → Fin (m_R i)) (hq' : ∑ j, (q' j : ℕ) < c_R i - 1) :
              (q' jLast : ℕ) + 1 < m_R i ∧
                ∑ j, (toHi q' j : ℕ) = (∑ j, (q' j : ℕ)) + 1 := by
            have hlast_lt : (q' jLast : ℕ) + 1 < m_R i := by
              have hle := Finset.single_le_sum (f := fun j : Fin d => (q' j : ℕ))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
              have := hcRm i; omega
            refine ⟨hlast_lt, ?_⟩
            have h := sum_update_nat (fun j => (q' j : ℕ)) jLast ((q' jLast : ℕ) + 1)
            have heq : ∑ j, (toHi q' j : ℕ) =
                ∑ j, Function.update (fun m => (q' m : ℕ)) jLast ((q' jLast : ℕ) + 1) j :=
              Finset.sum_congr rfl fun j _ => by
                by_cases hj : j = jLast <;> simp [toHi, hj, hlast_lt]
            rw [heq]; omega
          refine Finset.sum_nbij' toHi toLow ?_ ?_ ?_ ?_ ?_
          · intro q' hq'
            obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' (Finset.mem_filter.mp hq').2
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [hsum_hi]; have := (Finset.mem_filter.mp hq').2; omega
            · simp [toHi, hlast_lt]
          · intro q hq
            have hq_sum : ∑ j, (q j : ℕ) < c_R i :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
            have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
            have h := sum_update_nat (fun j => (q j : ℕ)) jLast ((q jLast : ℕ) - 1)
            have heq : ∑ j, (toLow q j : ℕ) =
                ∑ j, Function.update (fun m => (q m : ℕ)) jLast ((q jLast : ℕ) - 1) j :=
              Finset.sum_congr rfl fun j _ => by
                by_cases hj : j = jLast <;> simp [toLow, hj]
            rw [← heq] at h
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          · intro q' hq'
            obtain ⟨hlast_lt, _⟩ := htoHi q' (Finset.mem_filter.mp hq').2
            ext j
            by_cases hj : j = jLast <;> simp [toLow, toHi, hj, hlast_lt]
          · intro q hq
            have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
            have hlt_m : (q jLast : ℕ) - 1 + 1 < m_R i := by
              have := (q jLast).2; omega
            ext j
            by_cases hj : j = jLast
            · subst hj; simp [toHi, toLow, hlt_m]; omega
            · simp [toHi, toLow, hj]
          · intro q' hq'
            have hq'_lt : ∑ j, (q' j : ℕ) < c_R i - 1 := (Finset.mem_filter.mp hq').2
            obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' hq'_lt
            rw [hsum_hi]
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = jLast
            · subst hj
              have hcond : 1 ≤ (q' jLast : ℕ) + 1 ∧ (q' jLast : ℕ) + 1 < c_R i := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                omega
              simp [toHi, hlast_lt, φ, shiftUp, hcond]
            · simp only [toHi, hj, ↓reduceIte]
              have hqj_lt : (q' j : ℕ) + 1 < c_R i := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                omega
              exact (hφ_low j hj (u j) (q' j) hqj_lt).symm
        · simp only [c_R', w_R', Function.update_of_ne hi]
          refine Finset.sum_congr rfl fun q _ => ?_
          congr 1
          exact Finset.prod_congr rfl fun j _ => (hφ_other j i hi (u j) (q j)).symm
      let rem : Finset (Fin R) := Finset.univ \ D
      have hcard_rem : rem.card + D.card = R := by
        simpa [rem] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R' w_C u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
        rw [hT_red, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
        have hD0 : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            obtain ⟨j, hj, hkill⟩ := hDkill n hn
            have hj_ne : j ≠ jLast := by
              intro he; subst he; simp [jLast] at hj
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            simp [φ, hj_ne, hkill]
        rw [hD0, add_zero]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hle := ih (∑ i, c_R' i) hS' c_R' rfl hcR'm w_R' hwR' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) + (d - 1) =
          ∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1 := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else (d - 1) * (v - 1) + 1) c_R i₀ (c_R i₀ - 1)
        change (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) +
            (if c_R i₀ = 0 then 0 else (d - 1) * (c_R i₀ - 1) + 1) =
          (∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1) +
            (if c_R i₀ - 1 = 0 then 0 else (d - 1) * (c_R i₀ - 1 - 1) + 1) at h
        have h1 : c_R i₀ ≠ 0 := hi₀_ne
        have h2 : c_R i₀ - 1 ≠ 0 := by omega
        simp only [h1, h2, ↓reduceIte] at h
        have hmul : (d - 1) * (c_R i₀ - 1) =
            (d - 1) * (c_R i₀ - 1 - 1) + (d - 1) := by
          have hsub : c_R i₀ - 1 = (c_R i₀ - 1 - 1) + 1 := by omega
          conv_lhs => rw [hsub, mul_add, mul_one]
        omega
      omega

/-- Coordinate projection `(x, y) ↦ x i q` on `RealExpSpace m_R m_C`. -/
def projRealExp {ι_R ι_C : Type*} {m_R : ι_R → ℕ} {m_C : ι_C → ℕ}
    (i : ι_R) (q : Fin (m_R i)) : RealExpSpace m_R m_C →ₗ[ℝ] ℝ where
  toFun x := x.1 i q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate projection `(x, y) ↦ y k q` (`ℝ`-linear) on `RealExpSpace m_R m_C`. -/
def projCplxExp {ι_R ι_C : Type*} {m_R : ι_R → ℕ} {m_C : ι_C → ℕ}
    (k : ι_C) (q : Fin (m_C k)) : RealExpSpace m_R m_C →ₗ[ℝ] ℂ where
  toFun x := x.2 k q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Bundled `realExpForm` as an `ℝ`-multilinear map. -/
noncomputable def realExpMultilinearMap {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C]
    (d : ℕ) (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_R : ι_R → ℕ) (c_C : ι_C → ℕ)
    (w_R : ι_R → ℕ → ℝ) (w_C : ι_C → ℕ → ℂ) :
    MultilinearMap ℝ (fun _ : Fin d => RealExpSpace m_R m_C) ℝ :=
  (∑ i : ι_R, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i),
    w_R i (∑ j, (q j : ℕ)) •
      (MultilinearMap.mkPiAlgebra ℝ (Fin d) ℝ).compLinearMap
        (fun j => projRealExp i (q j))) +
  (∑ k : ι_C, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c_C k),
    ({ toFun := fun z : ℂ => (w_C k (∑ j, (q j : ℕ)) * z).re
       map_add' := fun a b => by simp [mul_add]
       map_smul' := fun r a => by simp [Complex.real_smul, Complex.mul_re]; ring } :
      ℂ →ₗ[ℝ] ℝ).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℝ (Fin d) ℂ).compLinearMap
        (fun j => projCplxExp k (q j))))

lemma realExpMultilinearMap_apply {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C]
    (d : ℕ) (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_R : ι_R → ℕ) (c_C : ι_C → ℕ)
    (w_R : ι_R → ℕ → ℝ) (w_C : ι_C → ℕ → ℂ)
    (u : Fin d → RealExpSpace m_R m_C) :
    realExpMultilinearMap d m_R m_C c_R c_C w_R w_C u =
      realExpForm d m_R m_C c_R c_C w_R w_C u := by
  simp [realExpMultilinearMap, realExpForm, realTruncForm, cplxTruncForm,
    projRealExp, projCplxExp]

open scoped Classical in
/-- Exponential-monomial evaluation vectors span `RealExpSpace m_R m_C` over `ℝ` when `rate` is
injective and lies in the closed upper half-plane. -/
lemma span_realExpEval_eq_top {ι : Type*} [Finite ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) (m : ι → ℕ) :
    Submodule.span ℝ
      (Set.range fun s : ℝ≥0 =>
        ((fun (i : {i : ι // (rate i).im = 0}) (q : Fin (m i.1)) =>
            ((s : ℝ) ^ (q : ℕ) / ((q : ℕ).factorial : ℝ)) *
              Real.exp ((rate i.1).re * (s : ℝ))),
         (fun (k : {i : ι // 0 < (rate i).im}) (q : Fin (m k.1)) =>
            ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
              exp (rate k.1 * (s : ℂ))))) = ⊤ := by
  cases nonempty_fintype ι
  let ι_R := {i : ι // (rate i).im = 0}
  let ι_C := {i : ι // 0 < (rate i).im}
  let m_R (i : ι_R) : ℕ := m i.1
  let m_C (k : ι_C) : ℕ := m k.1
  refine span_range_eq_top_of_dual fun L hL => ?_
  let a (i : ι_R) (q : Fin (m_R i)) : ℝ := L (embRealCoeff i q 1)
  let b (k : ι_C) (q : Fin (m_C k)) : ℂ :=
    L (0, singleCoeff k q 1) - I * L (0, singleCoeff k q I)
  have hL_expand (x : RealExpSpace m_R m_C) :
      L x = (∑ i : ι_R, ∑ q : Fin (m_R i), a i q * x.1 i q) +
        ∑ k : ι_C, ∑ q : Fin (m_C k), (b k q * x.2 k q).re := by
    have hx1 : x.1 = ∑ i : ι_R, ∑ q : Fin (m_R i), x.1 i q • singleRealCoeff i q (1 : ℝ) := by
      ext i₀ q₀
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single q₀]
        · simp
        · intro q _ hq
          simp [singleRealCoeff_of_ne_deg i₀ q q₀ 1 hq.symm]
        · simp
      · intro i _ hi
        exact Finset.sum_eq_zero fun q _ => by
          simp [singleRealCoeff_of_ne_idx i q 1 hi.symm]
      · simp
    have hx2 : x.2 = ∑ k : ι_C, ∑ q : Fin (m_C k),
        ((x.2 k q).re • singleCoeff k q (1 : ℂ) +
          (x.2 k q).im • singleCoeff k q I) := by
      ext k₀ q₀
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      rw [Finset.sum_eq_single k₀]
      · rw [Finset.sum_eq_single q₀]
        · simp [Complex.re_add_im]
        · intro q _ hq
          simp [singleCoeff_of_ne_deg k₀ q q₀ _ hq.symm]
        · simp
      · intro k _ hk
        exact Finset.sum_eq_zero fun q _ => by
          simp [singleCoeff_of_ne_idx k q _ hk.symm]
      · simp
    have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
    conv_lhs => rw [hx, hx1, hx2]
    rw [map_add]
    congr 1
    · have hp : (∑ i : ι_R, ∑ q : Fin (m_R i), x.1 i q • singleRealCoeff i q (1 : ℝ),
          (0 : CplxExpSpace m_C)) =
          ∑ i : ι_R, ∑ q : Fin (m_R i),
            x.1 i q • embRealCoeff (m_C := m_C) i q (1 : ℝ) := by
        ext <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum, embRealCoeff]
      rw [hp, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [map_smul, smul_eq_mul, mul_comm]
    · have hp : ((0 : ∀ i, Fin (m_R i) → ℝ), ∑ k : ι_C, ∑ q : Fin (m_C k),
          ((x.2 k q).re • singleCoeff k q (1 : ℂ) +
            (x.2 k q).im • singleCoeff k q I)) =
          ∑ k : ι_C, ∑ q : Fin (m_C k),
            ((x.2 k q).re • ((0 : ∀ i, Fin (m_R i) → ℝ), singleCoeff k q (1 : ℂ)) +
              (x.2 k q).im • ((0 : ∀ i, Fin (m_R i) → ℝ), singleCoeff k q I)) := by
        ext <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum, Complex.real_smul]
      rw [hp, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp [b, Complex.mul_re]
      ring
  let ν : ι ⊕ ι_C → ℂ := Sum.elim rate (fun k => starRingEnd ℂ (rate k.1))
  have hν : Function.Injective ν := injective_rates_with_conjugates hinj hup
  let polyR (i : ι_R) : ℂ[X] :=
    ∑ q : Fin (m_R i), C ((a i q : ℂ) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  let polyC (k : ι_C) : ℂ[X] :=
    ∑ q : Fin (m_C k), C ((b k q / 2) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  let polyConj (k : ι_C) : ℂ[X] :=
    ∑ q : Fin (m_C k), C ((starRingEnd ℂ (b k q) / 2) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  let P : ι ⊕ ι_C → ℂ[X] := Sum.elim
    (fun i => if h : (rate i).im = 0 then polyR ⟨i, h⟩
      else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩)
    polyConj
  have hP0 : ∀ p, P p = 0 := by
    refine eq_zero_of_sum_expPoly_eq_zero' hν P fun u hu => ?_
    have hs := (hL_expand
      ((fun (i : ι_R) (q : Fin (m_R i)) =>
          (u ^ (q : ℕ) / ((q : ℕ).factorial : ℝ)) * Real.exp ((rate i.1).re * u)),
       (fun (k : ι_C) (q : Fin (m_C k)) =>
          ((u : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate k.1 * (u : ℂ))))).symm.trans
      (hL ⟨u, hu.le⟩)
    dsimp only at hs
    have hsC : ((((∑ i : ι_R, ∑ q : Fin (m_R i),
        a i q * (u ^ (q : ℕ) / ((q : ℕ).factorial : ℝ) * Real.exp ((rate i.1).re * u))) +
      ∑ k : ι_C, ∑ q : Fin (m_C k),
        (b k q * ((u : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ) *
          exp (rate k.1 * (u : ℂ)))).re) : ℝ) : ℂ) = 0 := by
      rw [hs]; simp
    push_cast at hsC
    rw [← hsC]
    simp only [Fintype.sum_sum_type, P, ν, Sum.elim_inl, Sum.elim_inr]
    have hsplit_ι :
        (∑ i : ι, expPoly
          (if h : (rate i).im = 0 then polyR ⟨i, h⟩
           else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩) (rate i) u) =
        (∑ i : ι_R, expPoly (polyR i) (rate i.1) u) +
          ∑ k : ι_C, expPoly (polyC k) (rate k.1) u := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : ι => (rate i).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : ι => (rate i).im = 0)
          (Finset.univ.filter fun i : ι => (rate i).im = 0) (fun _ => by simp)
          (fun i => expPoly (if h : (rate i).im = 0 then polyR ⟨i, h⟩
            else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩) (rate i) u)]
        exact Finset.sum_congr rfl fun i _ => by simp [i.2]
      · have hiff (i : ι) : i ∈ Finset.univ.filter (fun i : ι => ¬ (rate i).im = 0) ↔
            0 < (rate i).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hup i) (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : ι => 0 < (rate i).im)
          (Finset.univ.filter fun i : ι => ¬ (rate i).im = 0) hiff
          (fun i => expPoly (if h : (rate i).im = 0 then polyR ⟨i, h⟩
            else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩) (rate i) u)]
        exact Finset.sum_congr rfl fun k _ => by simp [k.2.ne']
    rw [hsplit_ι, add_assoc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hrate_re : rate i.1 = ((rate i.1).re : ℂ) :=
        Complex.ext rfl (by simpa using i.2)
      rw [hrate_re]
      simp only [expPoly, polyR, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
        Finset.sum_mul, Complex.ofReal_re]
      exact Finset.sum_congr rfl fun q _ => by ring
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [expPoly, polyC, polyConj, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
        Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.re_eq_add_conj]
      simp only [map_mul, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_natCast,
        ← Complex.exp_conj]
      ring
  have ha0 (i : ι_R) (q : Fin (m_R i)) : a i q = 0 := by
    have hc := congrArg (fun r => r.coeff (q : ℕ)) (hP0 (Sum.inl i.1))
    simp only [P, Sum.elim_inl, i.2, ↓reduceDIte, polyR, finsetSum_coeff, coeff_C_mul,
      coeff_X_pow, mul_ite, mul_one, mul_zero, coeff_zero] at hc
    have hmem : ∃ q' : Fin (m_R i), (q' : ℕ) = (q : ℕ) := ⟨q, rfl⟩
    rw [Finset.sum_eq_single q] at hc
    · simp only [↓reduceIte] at hc
      have hfq : ((q : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℕ).factorial_ne_zero
      have haC : (a i q : ℂ) = 0 := (div_eq_zero_iff.mp hc).resolve_right hfq
      exact Complex.ofReal_eq_zero.mp haC
    · intro q' _ hne
      have hne_val : (q : ℕ) ≠ (q' : ℕ) := fun he => hne (Fin.ext he.symm)
      simp [hne_val]
    · simp
  have hb0 (k : ι_C) (q : Fin (m_C k)) : b k q = 0 := by
    have hc := congrArg (fun r => r.coeff (q : ℕ)) (hP0 (Sum.inl k.1))
    simp only [P, Sum.elim_inl, k.2.ne', ↓reduceDIte, polyC, finsetSum_coeff, coeff_C_mul,
      coeff_X_pow, mul_ite, mul_one, mul_zero, coeff_zero] at hc
    rw [Finset.sum_eq_single q] at hc
    · simp only [↓reduceIte] at hc
      have hfq : ((q : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℕ).factorial_ne_zero
      have hb2 : b k q / 2 = 0 := (div_eq_zero_iff.mp hc).resolve_right hfq
      exact (div_eq_zero_iff.mp hb2).resolve_right two_ne_zero
    · intro q' _ hne
      have hne_val : (q : ℕ) ≠ (q' : ℕ) := fun he => hne (Fin.ext he.symm)
      simp [hne_val]
    · simp
  exact LinearMap.ext fun x => by simp [hL_expand, ha0, hb0]


open scoped Classical in
/-- **Exact `d`-way real radial rank of any representation (`d ≥ 2`).**
Each real-rate component contributes `(d - 1) * deg P + 1` real `d`-way products, and each
nonreal conjugate-pair component contributes `2 * (d - 1) * deg P + d`. -/
theorem separableRank_radial_profile {d : ℕ} (hd : 2 ≤ d) {cs : List Component}
    (hcs : IsRepresentation cs) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      multiTotalCost d cs := by
  let comp : Fin cs.length → Component := fun i => cs[i]
  have hinj : Function.Injective fun i => (comp i).rate := by
    intro i j hij
    have h : (cs.map Component.rate)[(i : ℕ)]'(by simp) =
        (cs.map Component.rate)[(j : ℕ)]'(by simp) := by simpa [comp] using hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hcs.2).mp h)
  have hwf : ∀ i, (comp i).WellFormed := fun i => hcs.1 _ (List.getElem_mem _)
  have hprof : (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      fun x => ∑ i : Fin cs.length, (comp i).eval (∑ j, x j ^ 2) := by
    funext x
    exact (Fin.sum_univ_fun_getElem cs fun c => c.eval (∑ j, x j ^ 2)).symm
  have hcost : multiTotalCost d cs = ∑ i : Fin cs.length, (comp i).multiCost d :=
    (Fin.sum_univ_fun_getElem cs (Component.multiCost d)).symm
  rw [hprof, hcost]
  refine le_antisymm ?_ ?_
  · exact iInf₂_le _ (IsSumOfProducts.finsetSum fun i =>
      isSumOfProducts_radial_multiComponent hd (hwf i))
  · rw [separableRank_radial_eq_hankel d
      (fun t => ∑ i : Fin cs.length, (comp i).eval t)]
    refine le_iInf₂ fun R hR => ?_
    let m (i : Fin cs.length) : ℕ := (comp i).poly.natDegree + 1
    let ι_R := {i : Fin cs.length // ((comp i).rate).im = 0}
    let ι_C := {i : Fin cs.length // 0 < ((comp i).rate).im}
    let m_R (i : ι_R) : ℕ := m i.1
    let m_C (k : ι_C) : ℕ := m k.1
    let w_R (i : ι_R) (n : ℕ) : ℝ := (n.factorial : ℝ) * ((comp i.1).poly.coeff n).re
    let w_C (k : ι_C) (n : ℕ) : ℂ := (n.factorial : ℂ) * (comp k.1).poly.coeff n
    let v (s : ℝ≥0) : RealExpSpace m_R m_C :=
      ((fun i q => ((s : ℝ) ^ (q : ℕ) / ((q : ℕ).factorial : ℝ)) *
          Real.exp (((comp i.1).rate).re * (s : ℝ))),
       (fun k q => ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
          exp ((comp k.1).rate * (s : ℂ))))
    have hexp_unit (P : ℂ[X]) (μ : ℂ) (s : Fin d → ℝ≥0) :
        expPoly P μ (∑ j, (s j : ℝ)) =
          ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (P.natDegree + 1) =>
            ∑ j, (q j : ℕ) < P.natDegree + 1),
            (((∑ j, (q j : ℕ)).factorial : ℂ) * P.coeff (∑ j, (q j : ℕ))) *
              ∏ j : Fin d, ((s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
                exp (μ * (s j : ℂ)) := by
      simpa [truncForm] using sum_expPoly_eq_truncForm d (fun _ : Unit => μ) (fun _ : Unit => P) s
    have hK_eq : (fun s : Fin d → ℝ≥0 => ∑ i : Fin cs.length, (comp i).eval (∑ j, (s j : ℝ))) =
        fun s => realExpMultilinearMap d m_R m_C m_R m_C w_R w_C (fun j => v (s j)) := by
      funext s
      rw [realExpMultilinearMap_apply]
      simp only [realExpForm, realTruncForm, cplxTruncForm]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin cs.length => ((comp i).rate).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : Fin cs.length => ((comp i).rate).im = 0)
          (Finset.univ.filter fun i : Fin cs.length => ((comp i).rate).im = 0)
          (fun _ => by simp) (fun i => (comp i).eval (∑ j, (s j : ℝ)))]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hev : (comp i.1).eval (∑ j, (s j : ℝ)) =
            (expPoly (comp i.1).poly (comp i.1).rate (∑ j, (s j : ℝ))).re := rfl
        rw [hev, hexp_unit (comp i.1).poly (comp i.1).rate s, Complex.re_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        have hrate : (comp i.1).rate = (((comp i.1).rate).re : ℂ) :=
          Complex.ext rfl (by simpa using i.2)
        have hcoeff : (comp i.1).poly.coeff (∑ j, (q j : ℕ)) =
            (((comp i.1).poly.coeff (∑ j, (q j : ℕ))).re : ℂ) :=
          Complex.ext rfl (by simpa using (hwf i.1).2.2 i.2 (∑ j, (q j : ℕ)))
        have hcast_term :
            (((∑ j, (q j : ℕ)).factorial : ℂ) * (comp i.1).poly.coeff (∑ j, (q j : ℕ))) *
              (∏ j : Fin d, ((s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
                exp ((comp i.1).rate * (s j : ℂ))) =
            ((w_R i (∑ j, (q j : ℕ)) * ∏ j : Fin d, (v (s j)).1 i (q j) : ℝ) : ℂ) := by
          rw [hcoeff, hrate]
          dsimp [w_R, v]
          push_cast
          congr 1
        rw [hcast_term, Complex.ofReal_re]
      · have hiff (i : Fin cs.length) :
            i ∈ Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0) ↔
              0 < ((comp i).rate).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hwf i).2.1 (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : Fin cs.length => 0 < ((comp i).rate).im)
          (Finset.univ.filter fun i : Fin cs.length => ¬ ((comp i).rate).im = 0)
          hiff (fun i => (comp i).eval (∑ j, (s j : ℝ)))]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hev : (comp k.1).eval (∑ j, (s j : ℝ)) =
            (expPoly (comp k.1).poly (comp k.1).rate (∑ j, (s j : ℝ))).re := rfl
        rw [hev, hexp_unit (comp k.1).poly (comp k.1).rate s, Complex.re_sum]
    rw [hK_eq] at hR
    have hspan := span_realExpEval_eq_top hinj (fun i => (hwf i).2.1) m
    obtain ⟨ℓ, hℓ⟩ := exists_linear_factors_of_span_eq_top hspan
      (realExpMultilinearMap d m_R m_C m_R m_C w_R w_C) hR
    simp_rw [realExpMultilinearMap_apply] at hℓ
    have hwR : ∀ i : ι_R, 0 < m_R i → w_R i (m_R i - 1) ≠ 0 := fun i _ => by
      dsimp [w_R, m_R, m]
      have hlead : (comp i.1).poly.coeff (comp i.1).poly.natDegree ≠ 0 :=
        leadingCoeff_ne_zero.mpr (hwf i.1).1
      have him0 : ((comp i.1).poly.coeff (comp i.1).poly.natDegree).im = 0 :=
        (hwf i.1).2.2 i.2 _
      have hre_ne : ((comp i.1).poly.coeff (comp i.1).poly.natDegree).re ≠ 0 := fun h0 =>
        hlead (Complex.ext h0 him0)
      exact mul_ne_zero (Nat.cast_ne_zero.mpr ( Nat.factorial_ne_zero _ )) hre_ne
    have hwC : ∀ k : ι_C, 0 < m_C k → w_C k (m_C k - 1) ≠ 0 := fun k _ => by
      dsimp [w_C, m_C, m]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (leadingCoeff_ne_zero.mpr (hwf k.1).1)
    have hge := realExpForm_rank_ge hd m_R m_C m_C (fun _ => le_rfl) w_C hwC
      (∑ i, m_R i) m_R rfl (fun _ => le_rfl) w_R hwR R ℓ hℓ
    have hsum_cost : (∑ i : Fin cs.length, (comp i).multiCost d) =
        (∑ i : ι_R, if m_R i = 0 then 0 else (d - 1) * (m_R i - 1) + 1) +
        (∑ k : ι_C, if m_C k = 0 then 0 else 2 * (d - 1) * (m_C k - 1) + d) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin cs.length => ((comp i).rate).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : Fin cs.length => ((comp i).rate).im = 0)
          (Finset.univ.filter fun i : Fin cs.length => ((comp i).rate).im = 0)
          (fun _ => by simp) (fun i => (comp i).multiCost d)]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Component.multiCost, i.2, m_R, m]
      · have hiff (i : Fin cs.length) :
            i ∈ Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0) ↔
              0 < ((comp i).rate).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hwf i).2.1 (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : Fin cs.length => 0 < ((comp i).rate).im)
          (Finset.univ.filter fun i : Fin cs.length => ¬ ((comp i).rate).im = 0)
          hiff (fun i => (comp i).multiCost d)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Component.multiCost, k.2.ne', m_C, m]
    rw [hsum_cost]
    exact_mod_cast hge

/-- **Exact `d`-way real radial rank of a multi-Gaussian representation (`d ≥ 2`).** -/
theorem separableRank_radial_gaussian_profile {d : ℕ} (hd : 2 ≤ d) {cs : List Component}
    (hcs : IsGaussianRepresentation cs) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      gaussianTotalCost d cs := by
  rw [separableRank_radial_profile hd hcs.1, multiTotalCost_of_isGaussian hcs.2]

/-- **2-D Sufficiency.** The profile of a representation gives a 2-D radial kernel whose
separable rank is `totalCost cs`. -/
theorem separableRank_radial_two_profile {cs : List Component} (hcs : IsRepresentation cs) :
    separableRank (fun x : Fin 2 → ℝ => profile cs (∑ j, x j ^ 2)) = totalCost cs := by
  rw [separableRank_radial_profile (le_refl 2) hcs, multiTotalCost_two]

end KernelRank
