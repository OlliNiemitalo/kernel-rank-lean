import KernelRankLean.ExpPoly

/-!
# Conjugation of exponential polynomials

Conjugating an exponential polynomial conjugates its rate and its polynomial coefficients.
Distinct rates in the closed upper half-plane remain distinct after adjoining the conjugates
of the nonreal rates. These facts connect real components to complex exponential-polynomial sums.
-/

open Complex Polynomial

namespace KernelRank

/-- The exponential-polynomial relation for a family of distinct rates. -/
theorem eq_zero_of_sum_expPoly_eq_zero' {κ : Type*} [Fintype κ] {ν : κ → ℂ}
    (hν : Function.Injective ν) (P : κ → ℂ[X])
    (h : ∀ u : ℝ, 0 < u → ∑ k, expPoly (P k) (ν k) u = 0) : ∀ k, P k = 0 := by
  classical
  intro k
  have : Nonempty κ := ⟨k⟩
  let Q : ℂ → ℂ[X] := fun μ => P (Function.invFun ν μ)
  have hQ : ∀ k, Q (ν k) = P k := fun k => congrArg P (Function.leftInverse_invFun hν k)
  have hsum : ∀ u : ℝ, 0 < u →
      ∑ μ ∈ Finset.univ.image ν, expPoly (Q μ) μ u = 0 := by
    intro u hu
    rw [Finset.sum_image fun a _ b _ hab => hν hab]
    simpa [hQ] using h u hu
  rw [← hQ k]
  exact eq_zero_of_sum_expPoly_eq_zero _ Q hsum (ν k)
    (Finset.mem_image_of_mem ν (Finset.mem_univ k))

/-- The polynomial with conjugated coefficients. -/
noncomputable def conjPoly (A : ℂ[X]) : ℂ[X] := A.map (starRingEnd ℂ)

lemma eval_ofReal_conjPoly (A : ℂ[X]) (u : ℝ) :
    (conjPoly A).eval (u : ℂ) = starRingEnd ℂ (A.eval (u : ℂ)) := by
  rw [conjPoly, eval_map, ← eval₂_id, hom_eval₂, RingHom.comp_id, Complex.conj_ofReal]

lemma conj_expPoly (A : ℂ[X]) (μ : ℂ) (u : ℝ) :
    starRingEnd ℂ (expPoly A μ u) = expPoly (conjPoly A) (starRingEnd ℂ μ) u := by
  simp [expPoly, eval_ofReal_conjPoly, ← Complex.exp_conj, map_mul]

/-- Adjoining the conjugates of upper-half-plane rates introduces no duplicate rates. -/
lemma injective_rates_with_conjugates {ι : Type*} {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) :
    Function.Injective
      (Sum.elim rate (fun j : {i // 0 < (rate i).im} => starRingEnd ℂ (rate j.1))) := by
  rintro (a | a) (b | b) hab
  · exact congrArg Sum.inl (hinj hab)
  · have := congrArg Complex.im hab
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at this
    linarith [hup a, b.2]
  · have := congrArg Complex.im hab
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at this
    linarith [hup b, a.2]
  · exact congrArg Sum.inr
      (Subtype.ext (hinj (by simpa using congrArg (starRingEnd ℂ) hab)))

end KernelRank
