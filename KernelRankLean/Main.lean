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
* **Exact vs. border rank separation (`separableRank_radial_sq_mul_cos`,
  `separableRank_radial_sq_mul_cos_complex`,
  `exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos`):** on `ℝ^d` (`d ≥ 2`), the
  radial kernel `‖x‖² cos(‖x‖²)` has exact real rank `3 d - 2` and exact complexified rank `2 d`,
  while an explicit family of kernels of real rank at most `2 d` converges to it uniformly on
  every compact set—separating real border rank from exact real rank by at least `d - 2` for all
  `d ≥ 3`.
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

/-! ### Exact rank vs. border rank on `‖x‖² cos(‖x‖²)` -/

private lemma abs_prod_one_add_sub_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (h : ℝ) (hh : |h| ≤ 1) :
    |∏ j ∈ s, (1 + h * a j)| ≤ ∏ j ∈ s, (1 + a j) ∧
    |(∏ j ∈ s, (1 + h * a j)) - 1| ≤ |h| * ∏ j ∈ s, (1 + a j) ∧
    |(∏ j ∈ s, (1 + h * a j)) - 1 - h * ∑ j ∈ s, a j| ≤
      h ^ 2 * ∏ j ∈ s, (1 + a j) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [sq_nonneg]
  | @insert i s hi ih =>
    have hai : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨h1, h2, h3⟩ := ih has
    set P := ∏ j ∈ s, (1 + h * a j)
    set M := ∏ j ∈ s, (1 + a j)
    set S := ∑ j ∈ s, a j
    have hM : 0 ≤ M := Finset.prod_nonneg fun j hj => by linarith [has j hj]
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    refine ⟨?_, ?_, ?_⟩
    · calc
        |(1 + h * a i) * P| = |1 + h * a i| * |P| := abs_mul _ _
        _ ≤ (1 + |h| * a i) * M := by
          gcongr
          calc
            |1 + h * a i| ≤ |1| + |h * a i| := abs_add_le _ _
            _ = 1 + |h| * a i := by rw [abs_one, abs_mul, abs_of_nonneg hai]
        _ ≤ (1 + a i) * M := by
          gcongr
          nlinarith
    · have hid : (1 + h * a i) * P - 1 = (P - 1) + h * a i * P := by ring
      rw [hid]
      calc
        |(P - 1) + h * a i * P| ≤ |P - 1| + |h * a i * P| := abs_add_le _ _
        _ = |P - 1| + |h| * a i * |P| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hai]
        _ ≤ |h| * M + |h| * a i * M := by gcongr
        _ = |h| * ((1 + a i) * M) := by ring
    · have hid : (1 + h * a i) * P - 1 - h * (a i + S) =
          (P - 1 - h * S) + h * a i * (P - 1) := by ring
      rw [hid]
      calc
        |(P - 1 - h * S) + h * a i * (P - 1)|
            ≤ |P - 1 - h * S| + |h * a i * (P - 1)| := abs_add_le _ _
        _ = |P - 1 - h * S| + |h| * a i * |P - 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hai]
        _ ≤ h ^ 2 * M + |h| * a i * (|h| * M) := by gcongr
        _ = h ^ 2 * ((1 + a i) * M) := by
          have hsq : |h| * |h| = h ^ 2 := by rw [← sq_abs, sq]
          linear_combination a i * M * hsq

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

/-- **Border-rank separation (`d ≥ 3`).** On `ℝ^d` (`d ≥ 2`), there exists an explicit family `F h`
of real kernels with `separableRank (F h) ≤ 2 d` for every `h ∈ ℝ` that converges uniformly on
every compact subset `C ⊆ ℝ^d` to `‖x‖² cos(‖x‖²)` as `h → 0` (`h ≠ 0`). Combined with
`separableRank_radial_sq_mul_cos`, this proves that for every `d ≥ 3`, the set of kernels of real
separable rank at most `2 d` is not closed under compact-open limits, with an exact-minus-border
rank gap of at least `d - 2`. -/
theorem exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos {d : ℕ} (hd : 2 ≤ d) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (2 * d : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let G₁ (h : ℝ) (x : Fin d → ℝ) : ℂ :=
    ∏ j : Fin d, (1 + (h : ℂ) * (x j ^ 2 : ℝ)) * exp (I * (x j ^ 2 : ℝ))
  let G₀ (x : Fin d → ℝ) : ℂ :=
    ∏ j : Fin d, exp (I * (x j ^ 2 : ℝ))
  let F (h : ℝ) (x : Fin d → ℝ) : ℝ :=
    h⁻¹ * (G₁ h x).re + (-h⁻¹) * (G₀ x).re
  refine ⟨F, ?_, ?_⟩
  · intro h
    have hG₁ : IsSumOfProducts (fun x => (G₁ h x).re) d := by
      have hc : IsSumOfProducts (G₁ h) 1 :=
        ⟨fun _ j u => (1 + (h : ℂ) * (u ^ 2 : ℝ)) * exp (I * (u ^ 2 : ℝ)), fun x => by simp [G₁]⟩
      simpa using hc.re (by omega)
    have hG₀ : IsSumOfProducts (fun x => (G₀ x).re) d := by
      have hc : IsSumOfProducts G₀ 1 :=
        ⟨fun _ j u => exp (I * (u ^ 2 : ℝ)), fun x => by simp [G₀]⟩
      simpa using hc.re (by omega)
    have hF : IsSumOfProducts (F h) (d + d) :=
      (hG₁.smul h⁻¹).add (hG₀.smul (-h⁻¹))
    rw [show 2 * d = d + d by omega]
    exact iInf₂_le (d + d) hF
  · intro C hC
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hcontM : Continuous (fun x : Fin d → ℝ => ∏ j : Fin d, (1 + x j ^ 2)) := by fun_prop
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x ∈ C, ∏ j : Fin d, (1 + x j ^ 2) ≤ B := by
      rcases C.eq_empty_or_nonempty with rfl | hne
      · exact ⟨1, by simp⟩
      · obtain ⟨x₀, hx₀, hmax⟩ := hC.exists_isMaxOn hne hcontM.continuousOn
        exact ⟨∏ j : Fin d, (1 + x₀ j ^ 2), fun x hx => hmax hx⟩
    let B' : ℝ := max B 1
    have hB'_pos : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
    let δ : ℝ := min 1 (ε / (2 * B'))
    have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hε (mul_pos zero_lt_two hB'_pos))
    have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 ∧ |h| < δ := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ_pos)] with h hh0 hball
      exact ⟨hh0, by simpa [Real.dist_eq] using hball⟩
    filter_upwards [hev] with h ⟨hh0, hhδ⟩ x hxC
    have hh1 : |h| ≤ 1 := le_of_lt (lt_of_lt_of_le hhδ (min_le_left _ _))
    have hprod_G₁ : G₁ h x =
        ((∏ j : Fin d, (1 + h * x j ^ 2) : ℝ) : ℂ) * exp (I * (∑ j : Fin d, x j ^ 2 : ℝ)) := by
      simp only [G₁, Finset.prod_mul_distrib, ← Complex.exp_sum]
      congr 1
      · push_cast
        rfl
      · congr 1
        push_cast
        rw [Finset.mul_sum]
    have hprod_G₀ : G₀ x = exp (I * (∑ j : Fin d, x j ^ 2 : ℝ)) := by
      simp only [G₀, ← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.mul_sum]
    have hFx : F h x =
        h⁻¹ * ((∏ j : Fin d, (1 + h * x j ^ 2)) - 1) * Real.cos (∑ j : Fin d, x j ^ 2) := by
      rw [show F h x = h⁻¹ * (G₁ h x).re + (-h⁻¹) * (G₀ x).re from rfl, hprod_G₁, hprod_G₀]
      have h1 := re_ofReal_mul_exp_I_mul 1 (∑ j : Fin d, x j ^ 2)
      simp only [Complex.ofReal_one, one_mul] at h1
      rw [re_ofReal_mul_exp_I_mul, h1]
      ring
    rw [Real.dist_eq, hFx]
    set S := ∑ j : Fin d, x j ^ 2
    set P := ∏ j : Fin d, (1 + h * x j ^ 2)
    have hdiff : S * Real.cos S - h⁻¹ * (P - 1) * Real.cos S =
        -(h⁻¹ * (P - 1 - h * S) * Real.cos S) := by
      field_simp [hh0]
      ring
    rw [hdiff, abs_neg, abs_mul, abs_mul, abs_inv]
    have hbound := (abs_prod_one_add_sub_le Finset.univ (fun j => x j ^ 2)
      (fun j _ => sq_nonneg (x j)) h hh1).2.2
    have hM_le : ∏ j : Fin d, (1 + x j ^ 2) ≤ B' :=
      le_trans (hB x hxC) (le_max_left B 1)
    have hcos_le : |Real.cos S| ≤ 1 := Real.abs_cos_le_one S
    have hrem : |h|⁻¹ * |P - 1 - h * S| ≤ |h| * B' := by
      have hh_pos : 0 < |h| := abs_pos.mpr hh0
      calc
        |h|⁻¹ * |P - 1 - h * S| ≤ |h|⁻¹ * (h ^ 2 * ∏ j : Fin d, (1 + x j ^ 2)) := by gcongr
        _ ≤ |h|⁻¹ * (h ^ 2 * B') := by gcongr
        _ = |h| * B' := by
          have hsq : h ^ 2 = |h| * |h| := by rw [← sq_abs, sq]
          rw [hsq]
          field_simp [hh_pos.ne']
    calc
      |h|⁻¹ * |P - 1 - h * S| * |Real.cos S|
          ≤ (|h| * B') * 1 := mul_le_mul hrem hcos_le (abs_nonneg _) (by positivity)
      _ = |h| * B' := mul_one _
      _ < δ * B' := by gcongr
      _ ≤ (ε / (2 * B')) * B' := by
        gcongr
        exact min_le_right _ _
      _ = ε / 2 := by
        field_simp [hB'_pos.ne']
      _ < ε := half_lt_self hε

end KernelRank
