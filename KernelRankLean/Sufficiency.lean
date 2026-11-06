import KernelRankLean.ComplexRank
import KernelRankLean.Complexification

/-!
# Sufficiency: a sum of components has separable rank equal to its cost

Expand every nonreal component into two complex exponential polynomials at conjugate rates.
Real rates contribute one polynomial, with real coefficients. The complex exact-rank theorem
counts their multiplicities, and complexification preserves the real kernel's rank. Thus a real
rate of multiplicity `m` costs `m` terms, and a nonreal rate costs `2 m`.
-/

open Complex Polynomial NNReal

namespace KernelRank

/-- The profile of a family of components. -/
noncomputable def familyProfile {ι : Type*} [Fintype ι] (comp : ι → Component) (s : ℝ) : ℝ :=
  ∑ i, (comp i).eval s

/-- Conjugate expansion and complexification give the exact real translate-span dimension. -/
theorem finrank_translateSpan_familyProfile {ι : Type*} [Fintype ι] {comp : ι → Component}
    (hinj : Function.Injective fun i => (comp i).rate) (hwf : ∀ i, (comp i).WellFormed) :
    FiniteDimensional ℝ (translateSpan (familyProfile comp)) ∧
      Module.finrank ℝ (translateSpan (familyProfile comp)) = ∑ i, (comp i).cost := by
  classical
  let J := {i // 0 < (comp i).rate.im}
  let ν : ι ⊕ J → ℂ :=
    Sum.elim (fun i => (comp i).rate) (fun j => starRingEnd ℂ (comp j.1).rate)
  let P : ι ⊕ J → ℂ[X] := Sum.elim
    (fun i => if 0 < (comp i).rate.im then C (1 / 2) * (comp i).poly else (comp i).poly)
    (fun j => C (1 / 2) * conjPoly (comp j.1).poly)
  have hν : Function.Injective ν :=
    injective_rates_with_conjugates hinj (fun i => (hwf i).2.1)
  have hP : ∀ j, P j ≠ 0 := by
    rintro (i | j)
    · by_cases hi : 0 < (comp i).rate.im <;> simp [P, hi, (hwf i).1]
    · simpa [P, conjPoly] using
        mul_ne_zero (show C (1 / 2 : ℂ) ≠ 0 by norm_num)
          (Polynomial.map_ne_zero (f := starRingEnd ℂ) (hwf j.1).1)
  have hdeg : ∀ j, (P j).natDegree = (comp (Sum.elim id Subtype.val j)).poly.natDegree := by
    rintro (i | j)
    · by_cases hi : 0 < (comp i).rate.im
      · simp only [P, Sum.elim_inl, hi, ↓reduceIte, id_eq]
        exact natDegree_C_mul (by norm_num : (1 / 2 : ℂ) ≠ 0)
      · simp [P, hi]
    · simp only [P, Sum.elim_inr, conjPoly,
        natDegree_C_mul (by norm_num : (1 / 2 : ℂ) ≠ 0),
        natDegree_map_eq_of_injective (starRingEnd ℂ).injective]
  have hterm (i : ι) (t : ℝ) :
      ((comp i).eval t : ℂ) = expPoly (P (Sum.inl i)) (comp i).rate t +
        if 0 < (comp i).rate.im then
          expPoly (C (1 / 2) * conjPoly (comp i).poly) (starRingEnd ℂ (comp i).rate) t
        else 0 := by
    change ((expPoly (comp i).poly (comp i).rate t).re : ℂ) = _
    rw [Complex.re_eq_add_conj, conj_expPoly]
    by_cases hi : 0 < (comp i).rate.im
    · simp only [P, Sum.elim_inl, hi, ↓reduceIte, expPoly_C_mul]
      ring
    · have him : (comp i).rate.im = 0 := le_antisymm (not_lt.mp hi) (hwf i).2.1
      have hconj : conjPoly (comp i).poly = (comp i).poly := by
        ext k
        simpa only [conjPoly, coeff_map] using
          Complex.conj_eq_iff_im.mpr ((hwf i).2.2 him k)
      simp only [P, Sum.elim_inl, hi, ↓reduceIte, hconj,
        Complex.conj_eq_iff_im.mpr him, add_zero]
      ring
  have hprof (t : ℝ) :
      (familyProfile comp t : ℂ) = ∑ j, expPoly (P j) (ν j) t := by
    simp only [familyProfile, Complex.ofReal_sum, hterm, Finset.sum_add_distrib,
      Fintype.sum_sum_type, ν, P, Sum.elim_inl, Sum.elim_inr]
    congr 1
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter (fun i => 0 < (comp i).rate.im))
      (fun i => by simp)
      (fun i => expPoly (C (1 / 2) * conjPoly (comp i).poly)
        (starRingEnd ℂ (comp i).rate) t)
  have hsub (F : ι → ℕ) :
      ∑ j : J, F j.1 = ∑ i, if 0 < (comp i).rate.im then F i else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun i => 0 < (comp i).rate.im))
      (fun i => by simp) F).symm
  have hcost : ∑ j, ((P j).natDegree + 1) = ∑ i, (comp i).cost := by
    simp only [Fintype.sum_sum_type, hdeg, Sum.elim_inl, Sum.elim_inr]
    rw [hsub (fun i => (comp i).poly.natDegree + 1), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 0 < (comp i).rate.im
    · simp [hi, Component.cost, Component.multiplicity, hi.ne']
      omega
    · have him : (comp i).rate.im = 0 := le_antisymm (not_lt.mp hi) (hwf i).2.1
      simp [him, Component.cost, Component.multiplicity]
  obtain ⟨hfin, hdim⟩ := finrank_translateSpan_sum_expPoly hν P hP
  have hcomplex : (fun t => (familyProfile comp t : ℂ)) =
      fun t => ∑ j, expPoly (P j) (ν j) t := funext hprof
  rw [← hcomplex] at hfin hdim
  let : FiniteDimensional ℂ
      (rowSpan (fun u t : ℝ≥0 => (familyProfile comp (u + t) : ℂ))) := hfin
  refine ⟨finiteDimensional_rowSpan_ofReal
    (fun u t : ℝ≥0 => familyProfile comp (u + t)), ?_⟩
  exact (finrank_rowSpan_ofReal (fun u t : ℝ≥0 => familyProfile comp (u + t))).trans
    (hdim.trans hcost)

/-- **Sufficiency.** The profile of a representation gives a radial kernel whose separable rank
is the representation's total cost. -/
theorem separableRank_radial_profile {cs : List Component} (hcs : IsRepresentation cs) :
    separableRank (fun x y => profile cs (x ^ 2 + y ^ 2)) = totalCost cs := by
  let comp : Fin cs.length → Component := fun i => cs[i]
  have hinj : Function.Injective fun i => (comp i).rate := by
    intro i j hij
    have h : (cs.map Component.rate)[(i : ℕ)]'(by simp) =
        (cs.map Component.rate)[(j : ℕ)]'(by simp) := by
      simpa [comp] using hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hcs.2).mp h)
  have hwf : ∀ i, (comp i).WellFormed := fun i => hcs.1 _ (List.getElem_mem _)
  have hφ : profile cs = familyProfile comp :=
    funext fun s => (Fin.sum_univ_fun_getElem cs fun c => c.eval s).symm
  have hcost : totalCost cs = ∑ i, (comp i).cost :=
    (Fin.sum_univ_fun_getElem cs Component.cost).symm
  obtain ⟨hfin, hrank⟩ := finrank_translateSpan_familyProfile hinj hwf
  rw [hφ, hcost, ← hrank]
  exact separableRank_radial_eq_finrank _

end KernelRank
