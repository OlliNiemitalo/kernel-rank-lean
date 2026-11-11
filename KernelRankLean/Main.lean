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
-/

open Complex Polynomial

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

end KernelRank
