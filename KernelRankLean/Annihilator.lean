import KernelRankLean.ComplexRank
import KernelRankLean.Necessity

/-!
# Minimal differential annihilators

The complex exponential-polynomial expansion determines a profile's monic minimal annihilator:
the product of its distinct rate factors, each to its polynomial multiplicity. Its degree is
the exact radial rank. Derivatives are taken within `[0, ∞)`, including right derivatives at zero.
-/

open Polynomial NNReal

namespace KernelRank

/-- The least differential-annihilator order is the radial kernel's separable rank. -/
theorem exists_minimal_differential_annihilator (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] (hφ : ContinuousOn φ (Set.Ici 0)) :
    ∃ p : ℂ[X], p.Monic ∧
      separableRank (fun x y => φ (x ^ 2 + y ^ 2)) = p.natDegree ∧
      ∀ q : ℂ[X],
        (∀ t, 0 ≤ t → differentialOperator q (fun s => (φ s : ℂ)) t = 0) ↔ p ∣ q := by
  classical
  let ψ : ℝ → ℂ := fun t => (φ t : ℂ)
  let : FiniteDimensional ℂ (translateSpan ψ) := finiteDimensional_translateSpan_ofReal φ
  obtain ⟨S, Q, hψ⟩ := exists_sum_expPoly_of_finiteDimensional ψ
    (Complex.continuous_ofReal.comp_continuousOn hφ)
  let T := S.filter (fun μ => Q μ ≠ 0)
  let P (i : T) := Q i.1
  let rate (i : T) := i.1
  have hP (i : T) : P i ≠ 0 := (Finset.mem_filter.mp i.2).2
  have heq : Set.EqOn ψ (fun t => ∑ i, expPoly (P i) (rate i) t) (Set.Ici 0) := by
    intro t ht
    rw [hψ t ht]
    change (∑ μ ∈ S, expPoly (Q μ) μ t) = ∑ i : T, expPoly (Q i.1) i.1 t
    rw [Finset.sum_coe_sort T (fun μ => expPoly (Q μ) μ t)]
    symm
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro μ hμ hn
    have hQ : Q μ = 0 := by simpa [T, hμ] using hn
    simp [hQ]
  have hspan : translateSpan ψ = translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t) := by
    unfold translateSpan
    congr 2
    ext t u
    exact heq (add_nonneg u.2 t.2)
  obtain ⟨_, hrank⟩ := finrank_translateSpan_sum_expPoly Subtype.coe_injective P hP
  refine ⟨expPolyAnnihilator P rate, expPolyAnnihilator_monic P rate, ?_, fun q => ?_⟩
  · rw [separableRank_radial_eq_finrank, ← finrank_translateSpan_ofReal φ,
      hspan, hrank, expPolyAnnihilator_natDegree]
  · have h := differentialOperator_sum_expPoly_eq_zero_iff P rate Subtype.coe_injective hP q
    constructor
    · intro hq
      apply h.mp
      exact fun t ht => (differentialOperator_congr q heq ht).symm.trans (hq t ht)
    · intro hq t ht
      exact (differentialOperator_congr q heq ht).trans (h.mpr hq t ht)

/-- No nonzero constant-coefficient annihilator has order below the radial kernel's rank. -/
theorem separableRank_radial_le_natDegree_of_annihilator (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)]
    (hφ : ContinuousOn φ (Set.Ici 0)) {q : ℂ[X]} (hq : q ≠ 0)
    (hann : ∀ t, 0 ≤ t → differentialOperator q (fun s => (φ s : ℂ)) t = 0) :
    separableRank (fun x y => φ (x ^ 2 + y ^ 2)) ≤ q.natDegree := by
  obtain ⟨p, _, hrank, hp⟩ := exists_minimal_differential_annihilator φ hφ
  rw [hrank]
  exact_mod_cast natDegree_le_of_dvd ((hp q).mp hann) hq

end KernelRank
