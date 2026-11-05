import KernelRankLean.RealExpPoly
import KernelRankLean.Defs

/-!
# Regrouping a real exponential-polynomial sum into components

A real function `φ t = ∑ μ ∈ S, P μ (t) exp (μ t)` equals its real part
`∑ μ, Re (P μ (t) exp (μ t))`. The conjugate of a term has the conjugate rate, so the terms
with rates `μ` and `conj μ` merge into one component with rate in the upper half-plane; a real
rate's term keeps the real part of its coefficients. The nonzero results are a representation.
-/

open Complex Polynomial

namespace KernelRank

lemma Component.eval_eq (c : Component) (s : ℝ) : c.eval s = (expPoly c.poly c.rate s).re := rfl

lemma re_expPoly_conjPoly (A : ℂ[X]) (ν : ℂ) (u : ℝ) :
    (expPoly (conjPoly A) (starRingEnd ℂ ν) u).re = (expPoly A ν u).re := by
  rw [← conj_expPoly, Complex.conj_re]

/-- The weight of a rate's merged term: `1 / 2` for a real rate, which pairs with itself. -/
noncomputable def pairWeight (μ : ℂ) : ℝ := if μ.im = 0 then 1 / 2 else 1

/-- A sum over a conjugation-closed set of rates, folded onto the closed upper half-plane. -/
lemma sum_eq_sum_upperHalf (V : Finset ℂ) (hV : ∀ μ ∈ V, starRingEnd ℂ μ ∈ V) (f : ℂ → ℝ) :
    ∑ μ ∈ V, f μ = ∑ μ ∈ V.filter (fun μ => 0 ≤ μ.im),
      pairWeight μ * (f μ + f (starRingEnd ℂ μ)) := by
  classical
  have key : ∀ F : ℂ → ℝ, ∑ μ ∈ V, F (starRingEnd ℂ μ) = ∑ μ ∈ V, F μ := fun F =>
    Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ) hV hV (fun μ _ => Complex.conj_conj μ)
      (fun μ _ => Complex.conj_conj μ) (fun _ _ => rfl)
  let h : ℂ → ℝ := fun μ =>
    if 0 ≤ μ.im then pairWeight μ * (f μ + f (starRingEnd ℂ μ)) else 0
  have hpt : ∀ μ, h μ + h (starRingEnd ℂ μ) = f μ + f (starRingEnd ℂ μ) := by
    intro μ
    rcases lt_trichotomy μ.im 0 with hlt | heq | hgt
    · have h1 : ¬ 0 ≤ μ.im := not_le.mpr hlt
      have h2 : 0 ≤ (starRingEnd ℂ μ).im := by rw [Complex.conj_im]; linarith
      have h3 : (starRingEnd ℂ μ).im ≠ 0 := by rw [Complex.conj_im]; linarith
      simp only [h, h1, h2, h3, pairWeight, Complex.conj_conj, ↓reduceIte]
      ring
    · have hc : starRingEnd ℂ μ = μ := Complex.conj_eq_iff_im.mpr heq
      simp only [h, hc, heq, le_refl, pairWeight, ↓reduceIte]
      ring
    · have h1 : ¬ 0 ≤ (starRingEnd ℂ μ).im := by rw [Complex.conj_im]; linarith
      simp only [h, h1, hgt.le, hgt.ne', pairWeight, ↓reduceIte]
      ring
  have hsum : ∑ μ ∈ V, (h μ + h (starRingEnd ℂ μ)) = ∑ μ ∈ V, h μ + ∑ μ ∈ V, h μ := by
    rw [Finset.sum_add_distrib, key h]
  have hsum' : ∑ μ ∈ V, (f μ + f (starRingEnd ℂ μ)) = ∑ μ ∈ V, f μ + ∑ μ ∈ V, f μ := by
    rw [Finset.sum_add_distrib, key f]
  simp only [hpt] at hsum
  rw [Finset.sum_filter]
  change ∑ μ ∈ V, f μ = ∑ μ ∈ V, h μ
  linarith

/-- **Regrouping.** A real function that is, on `[0, ∞)`, a finite sum of exponential polynomials
with distinct rates is there the profile of a representation. -/
theorem exists_representation_of_sum_expPoly (φ : ℝ → ℝ) (S : Finset ℂ) (Q : ℂ → ℂ[X])
    (h : ∀ t, 0 ≤ t → (φ t : ℂ) = ∑ μ ∈ S, expPoly (Q μ) μ t) :
    ∃ cs : List Component, IsRepresentation cs ∧ ∀ t, 0 ≤ t → φ t = profile cs t := by
  classical
  let Q' : ℂ → ℂ[X] := fun μ => if μ ∈ S then Q μ else 0
  let V : Finset ℂ := S ∪ S.image (starRingEnd ℂ)
  have hV : ∀ μ ∈ V, starRingEnd ℂ μ ∈ V := by
    intro μ hμ
    simp only [V, Finset.mem_union, Finset.mem_image] at hμ ⊢
    rcases hμ with hμ | ⟨ν, hν, rfl⟩
    · exact Or.inr ⟨μ, hμ, rfl⟩
    · exact Or.inl (by simpa using hν)
  -- The merged polynomial of the rate `μ` and its conjugate.
  let R : ℂ → ℂ[X] := fun μ =>
    C (pairWeight μ : ℂ) * (Q' μ + conjPoly (Q' (starRingEnd ℂ μ)))
  let U := (V.filter fun μ => 0 ≤ μ.im).filter fun μ => R μ ≠ 0
  refine ⟨U.toList.map fun μ => ⟨μ, R μ⟩, ⟨?_, ?_⟩, ?_⟩
  · intro c hc
    simp only [List.mem_map, Finset.mem_toList] at hc
    obtain ⟨μ, hμ, rfl⟩ := hc
    simp only [U, Finset.mem_filter] at hμ
    refine ⟨hμ.2, hμ.1.2, fun him k => ?_⟩
    have hc : starRingEnd ℂ μ = μ := Complex.conj_eq_iff_im.mpr him
    simp [R, hc, conjPoly, coeff_map]
  · simpa [Function.comp_def] using Finset.nodup_toList U
  · intro t ht
    have hprof : profile (U.toList.map fun μ => ⟨μ, R μ⟩) t = ∑ μ ∈ U, (expPoly (R μ) μ t).re := by
      simp only [profile, List.map_map, Finset.sum_map_toList]
      rfl
    have hφ : φ t = ∑ μ ∈ V, (expPoly (Q' μ) μ t).re := by
      have h' := congrArg Complex.re (h t ht)
      rw [Complex.ofReal_re, Complex.re_sum] at h'
      calc φ t = ∑ μ ∈ S, (expPoly (Q' μ) μ t).re := by
            rw [h']
            exact Finset.sum_congr rfl fun μ hμ => by simp [Q', hμ]
        _ = ∑ μ ∈ V, (expPoly (Q' μ) μ t).re :=
            Finset.sum_subset Finset.subset_union_left fun μ _ hμ => by simp [Q', hμ]
    have hdrop : ∑ μ ∈ U, (expPoly (R μ) μ t).re =
        ∑ μ ∈ V.filter (fun μ => 0 ≤ μ.im), (expPoly (R μ) μ t).re := by
      refine Finset.sum_filter_of_ne fun μ _ hne => ?_
      intro h0
      apply hne
      simp [h0]
    rw [hprof, hdrop, hφ, sum_eq_sum_upperHalf V hV]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hc := re_expPoly_conjPoly (Q' (starRingEnd ℂ μ)) (starRingEnd ℂ μ) t
    rw [Complex.conj_conj] at hc
    simp only [R, expPoly_C_mul, expPoly_add, Complex.re_ofReal_mul, Complex.add_re, hc]

end KernelRank
