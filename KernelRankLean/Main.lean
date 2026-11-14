import KernelRankLean.Necessity
import KernelRankLean.MultiComplexRank
import KernelRankLean.MultiRealRank

/-!
# Main theorems

For any dimension `d ≥ 2`:

* **Classification (`separableRank_radial_lt_top_iff_exists`):** a real circularly symmetric
  kernel `x ↦ φ (∑ j, x j ^ 2)` on `ℝ^d`, with `φ` continuous on `[0, ∞)`, has finite `d`-way
  separable rank if and only if `φ` is, on `[0, ∞)`, the profile of an exponential-polynomial
  representation.
* **Exact `d`-D real radial rank (`separableRank_radial_eq_iff`):** a continuous real radial
  kernel on `ℝ^d` has `d`-way separable rank `N` if and only if `φ` agrees on `[0, ∞)` with a
  representation of `multiTotalCost d cs = N` (`(d - 1) * deg P + 1` per real rate and
  `2 * (d - 1) * deg P + d` per nonreal conjugate-pair rate). Specializing to `deg P = 0` gives
  `gaussianTotalCost d cs = r + d * c` (`separableRank_radial_gaussian_eq_iff`), and specializing
  to `d = 2` gives `totalCost cs = N` (`separableRank_radial_two_eq_iff`).
* **Exact `d`-D complex radial rank (`separableRank_radial_complex_eq_iff`):** a continuous
  complex radial kernel on `ℝ^d` has `d`-way separable rank `N` if and only if `ψ` agrees on
  `[0, ∞)` with a sum of nonzero complex exponential polynomials at distinct rates with
  `∑ μ, ((d - 1) * deg P_μ + 1) = N`.
* **General `d`-D border-rank bound and exact-vs.-border separation
  (`multiTotalCost_eq_borderTotalCost_add`,
  `exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile`,
  `separableRank_radial_sq_mul_cos`, `separableRank_radial_sq_mul_cos_complex`,
  `exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos`):** every well-formed radial
  profile `profile cs (‖x‖²)` on `ℝ^d` (`d ≥ 2`) is the uniform limit on every compact set of
  multi-Gaussian kernels of real rank at most `borderTotalCost d cs = multiTotalCost d cs -
  (d - 2) * ∑_c deg P_c`—strictly below its exact real rank whenever `d ≥ 3` and some `deg P_c ≥ 1`
  (in particular `2 d` vs. `3 d - 2` on `‖x‖² cos(‖x‖²)`).
-/

open Complex Polynomial Filter Topology

namespace KernelRank

/-- A radial kernel on `ℝ^d` only depends on its profile on `[0, ∞)`. -/
lemma radial_congr {d : ℕ} {𝕜 : Type*} {φ ψ : ℝ → 𝕜} (h : ∀ s, 0 ≤ s → φ s = ψ s) :
    (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = fun x => ψ (∑ j, x j ^ 2) :=
  funext fun x => h _ (Finset.sum_nonneg fun j _ => sq_nonneg (x j))

/-- **Classification (`d ≥ 2`).** A real radial kernel on `ℝ^d`, with profile continuous on
`[0, ∞)`, has finite `d`-way separable rank if and only if its profile is, on `[0, ∞)`, a sum of
components. -/
theorem separableRank_radial_lt_top_iff_exists {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) < ⊤ ↔
      ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s := by
  constructor
  · intro h
    have h2 : separableRank (fun x : Fin 2 → ℝ => φ (∑ j, x j ^ 2)) < ⊤ :=
      lt_of_le_of_lt (separableRank_radial_two_le hd φ) h
    have := (separableRank_radial_two_lt_top_iff φ).mp h2
    exact exists_representation_of_finiteDimensional φ hφ
  · rintro ⟨cs, _hcs, hφcs⟩
    rw [radial_congr hφcs]
    exact separableRank_radial_profile_lt_top hd cs

/-- **Exact `d`-D real radial rank (`d ≥ 2`).** A real radial kernel on `ℝ^d`, with profile
continuous on `[0, ∞)`, has `d`-way separable rank `N` if and only if its profile is, on
`[0, ∞)`, a sum of components with distinct rates costing `multiTotalCost d cs = N` rendering
terms in total (`(d - 1) * deg P + 1` per real rate and `2 * (d - 1) * deg P + d` per nonreal
conjugate-pair rate). -/
theorem separableRank_radial_eq_iff {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ multiTotalCost d cs = N := by
  constructor
  · intro h
    obtain ⟨cs, hcs, hφcs⟩ :=
      (separableRank_radial_lt_top_iff_exists hd φ hφ).mp (by rw [h]; simp)
    refine ⟨cs, hcs, hφcs, ?_⟩
    rw [radial_congr hφcs, separableRank_radial_profile hd hcs] at h
    exact_mod_cast h
  · rintro ⟨cs, hcs, hφcs, rfl⟩
    rw [radial_congr hφcs, separableRank_radial_profile hd hcs]

/-- **Exact 2-D real radial rank.** Specialization of `separableRank_radial_eq_iff` to `d = 2`,
where `multiTotalCost 2 cs = totalCost cs`. -/
theorem separableRank_radial_two_eq_iff (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ totalCost cs = N := by
  simpa only [multiTotalCost_two] using separableRank_radial_eq_iff (le_refl 2) φ hφ N

open scoped Classical in
/-- **Exact `d`-D complex radial rank (`d ≥ 2`).** A complex radial kernel on `ℝ^d`, with profile
continuous on `[0, ∞)`, has `d`-way separable rank `N` if and only if its profile agrees on
`[0, ∞)` with a finite sum of nonzero exponential polynomials at distinct rates whose `(d - 1)`-
weighted degrees sum to `N`. -/
theorem separableRank_radial_complex_eq_iff {d : ℕ} (hd : 2 ≤ d)
    (ψ : ℝ → ℂ) (hψ : ContinuousOn ψ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => ψ (∑ j, x j ^ 2)) = N ↔
      ∃ (S : Finset ℂ) (P : ℂ → ℂ[X]),
        (∀ μ ∈ S, P μ ≠ 0) ∧
        (∀ s, 0 ≤ s → ψ s = ∑ μ ∈ S, expPoly (P μ) μ s) ∧
        ∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1) = N := by
  constructor
  · intro h
    have h2 : separableRank (fun x : Fin 2 → ℝ => ψ (∑ j, x j ^ 2)) < ⊤ :=
      lt_of_le_of_lt (separableRank_radial_two_le hd ψ) (by rw [h]; simp)
    have : FiniteDimensional ℂ (translateSpan ψ) :=
      (separableRank_radial_two_lt_top_iff ψ).mp h2
    obtain ⟨S₀, P, hP₀⟩ := exists_sum_expPoly_of_finiteDimensional ψ hψ
    let S := S₀.filter fun μ => P μ ≠ 0
    have hPS : ∀ μ ∈ S, P μ ≠ 0 := fun μ hμ => (Finset.mem_filter.mp hμ).2
    have hψS : ∀ s, 0 ≤ s → ψ s = ∑ μ ∈ S, expPoly (P μ) μ s := by
      intro s hs
      rw [hP₀ s hs]
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun μ hμ₀ hμ => ?_
      have h0 : P μ = 0 := by simpa [S, hμ₀] using hμ
      simp [h0]
    refine ⟨S, P, hPS, hψS, ?_⟩
    rw [radial_congr hψS] at h
    have hcoe : (fun x : Fin d → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)) =
        fun x => ∑ μ : S, expPoly (P μ.1) μ.1 (∑ j, x j ^ 2) := by
      funext x
      exact (Finset.sum_coe_sort S (fun μ => expPoly (P μ) μ (∑ j, x j ^ 2))).symm
    rw [hcoe, separableRank_radial_sum_expPoly hd Subtype.val_injective
      (fun μ : S => P μ.1) (fun μ => hPS μ.1 μ.2)] at h
    have hsum : (∑ μ : S, ((d - 1) * (P μ.1).natDegree + 1)) =
        ∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1) :=
      Finset.sum_coe_sort S (fun μ => (d - 1) * (P μ).natDegree + 1)
    rw [← hsum]
    exact_mod_cast h
  · rintro ⟨S, P, hPS, hψS, rfl⟩
    rw [radial_congr hψS]
    have hcoe : (fun x : Fin d → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)) =
        fun x => ∑ μ : S, expPoly (P μ.1) μ.1 (∑ j, x j ^ 2) := by
      funext x
      exact (Finset.sum_coe_sort S (fun μ => expPoly (P μ) μ (∑ j, x j ^ 2))).symm
    have hsum : (∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1)) =
        ∑ μ : S, ((d - 1) * (P μ.1).natDegree + 1) :=
      (Finset.sum_coe_sort S (fun μ => (d - 1) * (P μ).natDegree + 1)).symm
    rw [hcoe, hsum]
    exact separableRank_radial_sum_expPoly hd Subtype.val_injective
      (fun μ : S => P μ.1) (fun μ => hPS μ.1 μ.2)

/-- **Exact `d`-D real multi-Gaussian rank (`d ≥ 2`).** Among multi-Gaussian radial kernels on
`ℝ^d`, the `d`-way separable rank equals `N` if and only if the Gaussian representation has
`gaussianTotalCost d cs = N` (`1` per real Gaussian, `d` per nonreal conjugate-pair Gaussian). -/
theorem separableRank_radial_gaussian_eq_iff {d : ℕ} (hd : 2 ≤ d) (φ : ℝ → ℝ)
    (hφ : ∃ cs : List Component, IsGaussianRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s)
    (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsGaussianRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ gaussianTotalCost d cs = N := by
  constructor
  · intro h
    obtain ⟨cs, hcs, hφcs⟩ := hφ
    refine ⟨cs, hcs, hφcs, ?_⟩
    rw [radial_congr hφcs, separableRank_radial_gaussian_profile hd hcs] at h
    exact_mod_cast h
  · rintro ⟨cs, hcs, hφcs, rfl⟩
    rw [radial_congr hφcs, separableRank_radial_gaussian_profile hd hcs]

/-! ### General `d`-D border-rank bound and exact-vs.-border rank separation -/

lemma abs_exp_sub_one_sub_le (y : ℝ) :
    |Real.exp y - 1 - y| ≤ y ^ 2 * Real.exp |y| := by
  have hconv : Convex ℝ (Set.Icc (-|y|) |y|) := convex_Icc _ _
  have hy_mem : y ∈ Set.Icc (-|y|) |y| := ⟨neg_abs_le y, le_abs_self y⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-|y|) |y| := ⟨neg_nonpos.mpr (abs_nonneg y), abs_nonneg y⟩
  have hexp_sub_one : ∀ t ∈ Set.Icc (-|y|) |y|, ‖Real.exp t - 1‖ ≤ |y| * Real.exp |y| := by
    intro t ht
    have h1 := hconv.norm_image_sub_le_of_norm_deriv_le (f := Real.exp)
      (fun z _ => (Real.hasDerivAt_exp z).differentiableAt)
      (fun z hz => by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
        exact Real.exp_le_exp.mpr hz.2)
      h0_mem ht
    rw [Real.exp_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have ht_abs : |t| ≤ |y| := abs_le.mpr ht
    calc
      ‖Real.exp t - 1‖ = |Real.exp t - 1| := Real.norm_eq_abs _
      _ ≤ Real.exp |y| * |t| := h1
      _ ≤ Real.exp |y| * |y| := mul_le_mul_of_nonneg_left ht_abs (Real.exp_pos _).le
      _ = |y| * Real.exp |y| := mul_comm _ _
  have h2 := hconv.norm_image_sub_le_of_norm_deriv_le (f := fun t => Real.exp t - t)
    (fun z _ => ((Real.hasDerivAt_exp z).sub (hasDerivAt_id z)).differentiableAt)
    (fun z hz => by
      have hd : deriv (fun t => Real.exp t - t) z = Real.exp z - 1 := by simp
      rw [hd]
      exact hexp_sub_one z hz)
    h0_mem hy_mem
  rw [Real.exp_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h2
  have heq1 : Real.exp y - y - 1 = Real.exp y - 1 - y := by ring
  have heq2 : |y| * Real.exp |y| * |y| = y ^ 2 * Real.exp |y| := by
    have : |y| * |y| = y ^ 2 := by rw [← sq_abs, sq]
    linear_combination Real.exp |y| * this
  rwa [heq1, heq2] at h2

private lemma natDegree_C_add_C_mul_X_le {R : Type*} [Semiring R] (a b : R) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  simpa using (Polynomial.natDegree_C_mul_X_pow_le b 1)

private lemma isSumOfProducts_component_expDiff {d : ℕ} (hd : 2 ≤ d) (c : Component)
    (hc : c.WellFormed) (h : ℝ) :
    IsSumOfProducts
      (fun x : Fin d → ℝ =>
        (c.poly.eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
          exp (c.rate * (∑ j, x j ^ 2 : ℝ))).re)
      (c.borderCost d) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty (Fin d)›
  let k := c.poly.natDegree
  by_cases him : c.rate.im = 0
  · have hcost : c.borderCost d = k + 1 := by simp [Component.borderCost, him, k]
    rw [hcost]
    have hcoeff_im : ∀ q, (c.poly.coeff q).im = 0 := hc.2.2 him
    let P_R : ℝ[X] :=
      ∑ q ∈ Finset.range (k + 1), Polynomial.C (c.poly.coeff q).re * Polynomial.X ^ q
    have hPR_deg : P_R.natDegree ≤ k := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun q hq => ?_
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
    let L_R : ℝ[X] := Polynomial.C (-h⁻¹) + Polynomial.C h⁻¹ * Polynomial.X
    have hLR_deg : L_R.natDegree ≤ 1 := natDegree_C_add_C_mul_X_le _ _
    let Q_R : ℝ[X] := P_R.comp L_R
    have hQR_deg : Q_R.natDegree < k + 1 := by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_comp_le.trans ?_)
      exact (Nat.mul_le_mul hPR_deg hLR_deg).trans (by simp)
    have hrate_eq : c.rate = (c.rate.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hpoly_eq (u : ℝ) : c.poly.eval (u : ℂ) = ((P_R.eval u : ℝ) : ℂ) := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self k)]
      change _ = (((Polynomial.evalRingHom u) P_R : ℝ) : ℂ)
      simp only [P_R, map_sum, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_sum, Complex.ofReal_mul,
        Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      apply Complex.ext <;> simp [hcoeff_im q]
    refine ⟨fun m j u =>
      (if j = i₀ then Q_R.coeff m else 1) *
        Real.exp ((c.rate.re + (m : ℕ) * h) * u ^ 2), fun x => ?_⟩
    dsimp only
    set s := ∑ j : Fin d, x j ^ 2
    let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
    have hexp_re : exp (c.rate * (s : ℂ)) = (Real.exp (c.rate.re * s) : ℂ) := by
      conv_lhs => rw [hrate_eq]
      rw [← Complex.ofReal_mul, Complex.ofReal_exp]
    change (c.poly.eval (u_s : ℂ) * exp (c.rate * (s : ℂ))).re = _
    rw [hpoly_eq u_s, hexp_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hLR_eval : L_R.eval (Real.exp (h * s)) = u_s := by
      simp [L_R, u_s]
      ring
    have hQR_eval : P_R.eval u_s = ∑ m : Fin (k + 1), Q_R.coeff m * Real.exp (h * s) ^ (m : ℕ) := by
      rw [← hLR_eval, ← Polynomial.eval_comp,
        Polynomial.eval_eq_sum_range' hQR_deg,
        Fin.sum_univ_eq_sum_range (fun m => Q_R.coeff m * Real.exp (h * s) ^ m) (k + 1)]
    rw [hQR_eval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hprod : (∏ j : Fin d,
        (if j = i₀ then Q_R.coeff m else 1) *
          Real.exp ((c.rate.re + (m : ℕ) * h) * x j ^ 2)) =
        Q_R.coeff m * ∏ j : Fin d, Real.exp ((c.rate.re + (m : ℕ) * h) * x j ^ 2) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then Q_R.coeff m else (1 : ℝ)) = 1 :=
        Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
      simp [her]
    rw [hprod, ← Real.exp_sum, ← Finset.mul_sum, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    have : (m : ℕ) * (h * s) + c.rate.re * s = (c.rate.re + (m : ℕ) * h) * s := by ring
    rw [this]
  · have hcost : c.borderCost d = (k + 1) * d := by
      simp [Component.borderCost, him, k, mul_comm]
    rw [hcost]
    let L_C : ℂ[X] := Polynomial.C (-(h : ℂ)⁻¹) + Polynomial.C ((h : ℂ)⁻¹) * Polynomial.X
    have hLC_deg : L_C.natDegree ≤ 1 := natDegree_C_add_C_mul_X_le _ _
    let Q_C : ℂ[X] := c.poly.comp L_C
    have hQC_deg : Q_C.natDegree < k + 1 := by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_comp_le.trans ?_)
      exact (Nat.mul_le_mul le_rfl hLC_deg).trans (by simp [k])
    have hcpx : IsSumOfProducts
        (fun x : Fin d → ℝ =>
          c.poly.eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
            exp (c.rate * (∑ j, x j ^ 2 : ℝ)))
        (k + 1) := by
      refine ⟨fun m j u =>
        (if j = i₀ then Q_C.coeff m else 1) *
          exp ((c.rate + (m : ℕ) * (h : ℂ)) * (u ^ 2 : ℝ)), fun x => ?_⟩
      dsimp only
      set s := ∑ j : Fin d, x j ^ 2
      let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
      have hLC_eval : L_C.eval (exp ((h : ℂ) * (s : ℂ))) = (u_s : ℂ) := by
        simp only [L_C, u_s, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
          Polynomial.eval_X, ← Complex.ofReal_mul]
        rw [← Complex.ofReal_exp]
        push_cast
        ring
      change c.poly.eval (u_s : ℂ) * exp (c.rate * (s : ℂ)) = _
      rw [← hLC_eval, ← Polynomial.eval_comp, Polynomial.eval_eq_sum_range' hQC_deg,
        ← Fin.sum_univ_eq_sum_range (fun m => Q_C.coeff m * exp ((h : ℂ) * (s : ℂ)) ^ m) (k + 1),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hprod : (∏ j : Fin d,
          (if j = i₀ then Q_C.coeff m else 1) *
            exp ((c.rate + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ))) =
          Q_C.coeff m * ∏ j : Fin d, exp ((c.rate + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) := by
        rw [Finset.prod_mul_distrib]
        congr 1
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
        have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then Q_C.coeff m else (1 : ℂ)) = 1 :=
          Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
        simp [her]
      rw [hprod, ← Complex.exp_sum, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
      have hs_cast : (∑ j : Fin d, (c.rate + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) =
          (c.rate + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by
        rw [← Finset.mul_sum]
        push_cast [s]
        rfl
      rw [hs_cast]
      have : (m : ℕ) * ((h : ℂ) * (s : ℂ)) + c.rate * (s : ℂ) =
          (c.rate + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by ring
      rw [this]
    exact hcpx.re (by omega)

private lemma exists_isSumOfProducts_borderTotalCost_tendstoUniformlyOn
    {d : ℕ} (hd : 2 ≤ d) (cs : List Component) (hcs : ∀ c ∈ cs, c.WellFormed) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, IsSumOfProducts (F h) (borderTotalCost d cs)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => profile cs (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
  induction cs with
  | nil =>
    refine ⟨fun _ _ => 0, fun _ => ?_, fun C _ => ?_⟩
    · dsimp only [borderTotalCost, List.map_nil, List.sum_nil]
      exact ⟨fun n => n.elim0, fun _ => by simp⟩
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa [profile] using hε
  | cons c cs ih =>
    have hc : c.WellFormed := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, c'.WellFormed := fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    obtain ⟨F', hrank', htend'⟩ := ih hcs'
    let Fc (h : ℝ) (x : Fin d → ℝ) : ℝ :=
      (c.poly.eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
        exp (c.rate * (∑ j, x j ^ 2 : ℝ))).re
    refine ⟨fun h x => Fc h x + F' h x, fun h => ?_, fun C hC => ?_⟩
    · exact (isSumOfProducts_component_expDiff hd c hc h).add (hrank' h)
    · have hFc_tend : TendstoUniformlyOn Fc (fun x => c.eval (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hcontS : Continuous (fun x : Fin d → ℝ => ∑ j : Fin d, x j ^ 2) := by fun_prop
        obtain ⟨B, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, ∑ j : Fin d, x j ^ 2 ≤ B := by
          rcases C.eq_empty_or_nonempty with rfl | hne
          · exact ⟨0, le_rfl, by simp⟩
          · obtain ⟨x₀, hx₀, hmax⟩ := hC.exists_isMaxOn hne hcontS.continuousOn
            exact ⟨∑ j : Fin d, x₀ j ^ 2,
              Finset.sum_nonneg fun j _ => sq_nonneg (x₀ j), fun x hx => hmax hx⟩
        let g (p : ℝ × ℝ) : ℝ := (c.poly.eval (p.1 : ℂ) * exp (c.rate * (p.2 : ℂ))).re
        have hg_cont : Continuous g := by
          refine Complex.continuous_re.comp (Continuous.mul ?_ ?_)
          · exact c.poly.continuous_aeval.comp (Complex.continuous_ofReal.comp continuous_fst)
          · exact Complex.continuous_exp.comp
              (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))
        let K_box : Set (ℝ × ℝ) := Set.Icc (-1) (B + 1) ×ˢ Set.Icc 0 B
        have hK_comp : IsCompact K_box := isCompact_Icc.prod isCompact_Icc
        obtain ⟨δ_u, hδ_u_pos, hδ_u⟩ := Metric.uniformContinuousOn_iff.mp
          (hK_comp.uniformContinuousOn_of_continuous hg_cont.continuousOn) ε hε
        let M_B : ℝ := max 1 ((B + 1) ^ 2 * Real.exp (B + 1))
        have hM_B_pos : 0 < M_B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        let η : ℝ := min 1 (min δ_u 1 / (2 * M_B))
        have hη_pos : 0 < η :=
          lt_min zero_lt_one (div_pos (lt_min hδ_u_pos zero_lt_one) (mul_pos zero_lt_two hM_B_pos))
        have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 ∧ |h| < η := by
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hη_pos)] with h hh0 hball
          exact ⟨hh0, by simpa [Real.dist_eq] using hball⟩
        filter_upwards [hev] with h ⟨hh0, hhη⟩ x hxC
        set s := ∑ j : Fin d, x j ^ 2
        have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
        have hsB : s ≤ B := hB.2 x hxC
        have hh1 : |h| ≤ 1 := le_of_lt (lt_of_lt_of_le hhη (min_le_left _ _))
        let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
        have hu_diff : |u_s - s| < min δ_u 1 := by
          have hh_pos : 0 < |h| := abs_pos.mpr hh0
          have hsub : u_s - s = h⁻¹ * (Real.exp (h * s) - 1 - h * s) := by
            dsimp only [u_s]
            field_simp [hh0]
          have habs_hs : |h * s| ≤ B + 1 := by
            rw [abs_mul, abs_of_nonneg hs0]
            nlinarith
          have hexp_b := abs_exp_sub_one_sub_le (h * s)
          have hrem : |u_s - s| ≤ |h| * M_B := by
            rw [hsub, abs_mul, abs_inv]
            calc
              |h|⁻¹ * |Real.exp (h * s) - 1 - h * s|
                  ≤ |h|⁻¹ * ((h * s) ^ 2 * Real.exp |h * s|) := by gcongr
              _ = |h| * (s ^ 2 * Real.exp |h * s|) := by
                  have : (h * s) ^ 2 = |h| * |h| * s ^ 2 := by
                    rw [mul_pow, ← sq_abs h, sq]
                  rw [this]
                  field_simp [hh_pos.ne']
              _ ≤ |h| * ((B + 1) ^ 2 * Real.exp (B + 1)) := by
                  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
                  exact mul_le_mul (pow_le_pow_left₀ hs0 (by linarith) 2)
                    (Real.exp_le_exp.mpr habs_hs) (Real.exp_pos _).le (sq_nonneg _)
              _ ≤ |h| * M_B := mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg h)
          calc
            |u_s - s| ≤ |h| * M_B := hrem
            _ < η * M_B := mul_lt_mul_of_pos_right hhη hM_B_pos
            _ ≤ (min δ_u 1 / (2 * M_B)) * M_B :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hM_B_pos.le
            _ = min δ_u 1 / 2 := by field_simp [hM_B_pos.ne']
            _ < min δ_u 1 := half_lt_self (lt_min hδ_u_pos zero_lt_one)
        have hu_box : (u_s, s) ∈ K_box := by
          have hu1 : |u_s - s| ≤ 1 := le_of_lt (lt_of_lt_of_le hu_diff (min_le_right _ _))
          rw [abs_le] at hu1
          exact ⟨⟨by linarith, by linarith⟩, ⟨hs0, hsB⟩⟩
        have hs_box : (s, s) ∈ K_box := ⟨⟨by linarith, by linarith⟩, ⟨hs0, hsB⟩⟩
        have hdist : dist (s, s) (u_s, s) < δ_u := by
          rw [Prod.dist_eq]
          simp only [dist_self, max_eq_left dist_nonneg]
          rw [Real.dist_eq, abs_sub_comm]
          exact lt_of_lt_of_le hu_diff (min_le_left _ _)
        change dist (g (s, s)) (g (u_s, s)) < ε
        exact hδ_u (s, s) hs_box (u_s, s) hu_box hdist
      have hprof_cons : (fun x : Fin d → ℝ => profile (c :: cs) (∑ j, x j ^ 2)) =
          fun x => c.eval (∑ j, x j ^ 2) + profile cs (∑ j, x j ^ 2) := by
        funext x
        simp [profile]
      rw [hprof_cons]
      exact hFc_tend.add (htend' C hC)

/-- **General `d`-D border-rank bound (`d ≥ 2`).** For every list `cs` of well-formed components,
there exists an explicit family `F h` of real kernels on `ℝ^d` having `d`-way separable rank at
most `borderTotalCost d cs` for every `h ∈ ℝ` and converging uniformly on every compact subset
`C ⊆ ℝ^d` to `x ↦ profile cs (∑ j, x j ^ 2)` as `h → 0` (`h ≠ 0`). Combined with
`separableRank_radial_profile` and `multiTotalCost_eq_borderTotalCost_add`, every representation
in dimension `d ≥ 3` has an exact-minus-border real rank gap of at least
`(d - 2) * ∑_{c ∈ cs} deg P_c`. -/
theorem exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile
    {d : ℕ} (hd : 2 ≤ d) (cs : List Component) (hcs : ∀ c ∈ cs, c.WellFormed) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (borderTotalCost d cs : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => profile cs (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
  obtain ⟨F, hF, htend⟩ := exists_isSumOfProducts_borderTotalCost_tendstoUniformlyOn hd cs hcs
  exact ⟨F, fun h => iInf₂_le _ (hF h), htend⟩

private lemma re_ofReal_mul_exp_I_mul (r s : ℝ) :
    (((r : ℂ) * exp (I * (s : ℂ))).re) = r * Real.cos s := by
  rw [mul_comm I (s : ℂ), exp_mul_I]
  simp [mul_add, Complex.cos_ofReal_re]

/-- Exact `d`-way real separable rank of `‖x‖² cos(‖x‖²)` on `ℝ^d` (`d ≥ 2`) is `3 d - 2`. -/
theorem separableRank_radial_sq_mul_cos {d : ℕ} (hd : 2 ≤ d) :
    separableRank (fun x : Fin d → ℝ => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)) =
      (3 * d - 2 : ℕ) := by
  let c : Component := ⟨I, Polynomial.X⟩
  have hwf : IsRepresentation [c] := by
    refine ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton, forall_eq]
    refine ⟨Polynomial.X_ne_zero, by simp [c], fun h => by simp [c] at h⟩
  have heval (s : ℝ) : s * Real.cos s = profile [c] s := by
    simp only [profile, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.eval, c, Polynomial.eval_X]
    exact (re_ofReal_mul_exp_I_mul s s).symm
  have hfun : (fun x : Fin d → ℝ => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)) =
      fun x => profile [c] (∑ j, x j ^ 2) := funext fun x => heval _
  rw [hfun, separableRank_radial_profile hd hwf]
  have hcost : multiTotalCost d [c] = 3 * d - 2 := by
    have : c.rate.im ≠ 0 := by simp [c]
    simp only [multiTotalCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.multiCost, this, ↓reduceIte, c, Polynomial.natDegree_X]
    omega
  rw [hcost]

/-- Exact `d`-way complex separable rank of `‖x‖² cos(‖x‖²)` on `ℝ^d` (`d ≥ 2`) is `2 d`. -/
theorem separableRank_radial_sq_mul_cos_complex {d : ℕ} (hd : 2 ≤ d) :
    separableRank (fun x : Fin d → ℝ =>
      (((∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2) : ℝ) : ℂ)) = (2 * d : ℕ) := by
  classical
  let S : Finset ℂ := {I, -I}
  let P : ℂ → ℂ[X] := fun _ => Polynomial.C (1 / 2 : ℂ) * Polynomial.X
  have hneI : (I : ℂ) ≠ -I := by
    intro h
    have : (1 : ℝ) = -1 := by simpa using congrArg Complex.im h
    linarith
  have hP0 : ∀ μ ∈ S, P μ ≠ 0 := fun _ _ => by simp [P]
  have hdeg : ∀ μ, (P μ).natDegree = 1 := fun _ => by
    rw [Polynomial.natDegree_C_mul (by norm_num : (1 / 2 : ℂ) ≠ 0), Polynomial.natDegree_X]
  have hcont : ContinuousOn
      (fun s : ℝ => (((s * Real.cos s : ℝ) : ℂ))) (Set.Ici 0) :=
    (Complex.continuous_ofReal.comp (continuous_id.mul Real.continuous_cos)).continuousOn
  rw [separableRank_radial_complex_eq_iff hd _ hcont (2 * d)]
  refine ⟨S, P, hP0, ?_, ?_⟩
  · intro s _hs
    simp only [S, Finset.sum_pair hneI, expPoly, P, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Complex.ofReal_mul, Complex.ofReal_cos]
    rw [Complex.cos]
    have h1 : (s : ℂ) * I = I * (s : ℂ) := mul_comm _ _
    have h2 : -(s : ℂ) * I = -I * (s : ℂ) := by ring
    rw [h1, h2]
    ring
  · simp [S, Finset.sum_pair hneI, hdeg]
    omega

/-- **Border-rank separation on `‖x‖² cos(‖x‖²)` (`d ≥ 3`).** Specialization of
`exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile` to `[⟨I, X⟩]`: on `ℝ^d`
(`d ≥ 2`), there exists an explicit family `F h` of real kernels with `separableRank (F h) ≤ 2 d`
converging uniformly on every compact subset `C ⊆ ℝ^d` to `‖x‖² cos(‖x‖²)`. -/
theorem exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos {d : ℕ} (hd : 2 ≤ d) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (2 * d : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by
  let c : Component := ⟨I, Polynomial.X⟩
  have hwf : ∀ c' ∈ ([c] : List Component), c'.WellFormed := by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨Polynomial.X_ne_zero, by simp [c], fun h => by simp [c] at h⟩
  obtain ⟨F, hrank, htend⟩ :=
    exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile hd [c] hwf
  have hcost : borderTotalCost d [c] = 2 * d := by
    have : c.rate.im ≠ 0 := by simp [c]
    simp only [borderTotalCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.borderCost, this, ↓reduceIte, c, Polynomial.natDegree_X]
    ring
  have hfun : (fun x : Fin d → ℝ => profile [c] (∑ j, x j ^ 2)) =
      fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2) := by
    funext x
    simp only [profile, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.eval, c, Polynomial.eval_X]
    exact re_ofReal_mul_exp_I_mul _ _
  rw [hcost] at hrank
  rw [hfun] at htend
  exact ⟨F, hrank, htend⟩

end KernelRank
