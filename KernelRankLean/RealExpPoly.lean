import KernelRankLean.ExpPoly

/-!
# Real parts of exponential polynomials vanish only trivially

If `∑ i, Re (A i (u) · exp (λ i u)) = 0` for all `u > 0`, with distinct rates in the closed upper
half-plane, then `A i = 0` for every non-real rate, and `A i` has purely imaginary coefficients
for every real rate (those make no real part). Write `Re z = (z + conj z) / 2`: the conjugate
terms have the conjugate rates, which lie in the open lower half-plane, so all rates involved are
distinct, and the complex statement applies.
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
  have hsum : ∀ u : ℝ, 0 < u → ∑ μ ∈ Finset.univ.image ν, expPoly (Q μ) μ u = 0 := by
    intro u hu
    rw [Finset.sum_image fun a _ b _ hab => hν hab]
    simpa [hQ] using h u hu
  rw [← hQ k]
  exact eq_zero_of_sum_expPoly_eq_zero _ Q hsum (ν k) (Finset.mem_image_of_mem ν (Finset.mem_univ k))

/-- The polynomial with conjugated coefficients. -/
noncomputable def conjPoly (A : ℂ[X]) : ℂ[X] := A.map (starRingEnd ℂ)

lemma eval_ofReal_conjPoly (A : ℂ[X]) (u : ℝ) :
    (conjPoly A).eval (u : ℂ) = starRingEnd ℂ (A.eval (u : ℂ)) := by
  rw [conjPoly, eval_map, ← eval₂_id, hom_eval₂, RingHom.comp_id, Complex.conj_ofReal]

lemma conj_expPoly (A : ℂ[X]) (μ : ℂ) (u : ℝ) :
    starRingEnd ℂ (expPoly A μ u) = expPoly (conjPoly A) (starRingEnd ℂ μ) u := by
  simp [expPoly, eval_ofReal_conjPoly, ← Complex.exp_conj, map_mul]

/-- **Real parts of exponential polynomials vanish only trivially.** -/
theorem eq_zero_of_sum_re_expPoly_eq_zero {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) (A : ι → ℂ[X])
    (h : ∀ u : ℝ, 0 < u → ∑ i, (expPoly (A i) (rate i) u).re = 0) (i : ι) :
    (0 < (rate i).im → A i = 0) ∧ ((rate i).im = 0 → ∀ k, ((A i).coeff k).re = 0) := by
  classical
  -- The rates `rate i` and, for the non-real ones, their conjugates.
  let ι' := {i // 0 < (rate i).im}
  let ν : ι ⊕ ι' → ℂ := Sum.elim rate fun j => starRingEnd ℂ (rate j.1)
  have hν : Function.Injective ν := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hinj hab)
    · have := congrArg Complex.im hab
      simp only [ν, Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at this
      linarith [hup a, b.2]
    · have := congrArg Complex.im hab
      simp only [ν, Sum.elim_inl, Sum.elim_inr, Complex.conj_im] at this
      linarith [hup b, a.2]
    · exact congrArg Sum.inr (Subtype.ext (hinj (by simpa [ν] using congrArg (starRingEnd ℂ) hab)))
  let half : ℂ[X] := C (1 / 2)
  let P : ι ⊕ ι' → ℂ[X] := Sum.elim
    (fun i => if 0 < (rate i).im then half * A i else half * (A i + conjPoly (A i)))
    (fun j => half * conjPoly (A j.1))
  -- Termwise, `Re (A e) = (A e + conj (A e)) / 2`.
  have hterm : ∀ u : ℝ, ∀ i : ι, ((expPoly (A i) (rate i) u).re : ℂ) =
      expPoly (P (Sum.inl i)) (rate i) u +
        if 0 < (rate i).im then expPoly (half * conjPoly (A i)) (starRingEnd ℂ (rate i)) u else 0 := by
    intro u i
    rw [Complex.re_eq_add_conj, conj_expPoly]
    by_cases hi : 0 < (rate i).im
    · simp only [P, Sum.elim_inl, hi, ↓reduceIte, half, expPoly_C_mul]
      ring
    · have hreal : starRingEnd ℂ (rate i) = rate i :=
        Complex.conj_eq_iff_im.mpr (le_antisymm (not_lt.mp hi) (hup i))
      simp only [P, Sum.elim_inl, hi, ↓reduceIte, half, expPoly_C_mul, expPoly_add, hreal,
        add_zero]
      ring
  have hsum : ∀ u : ℝ, 0 < u → ∑ k, expPoly (P k) (ν k) u = 0 := by
    intro u hu
    have := congrArg (fun r : ℝ => (r : ℂ)) (h u hu)
    simp only [Complex.ofReal_sum, hterm, Finset.sum_add_distrib, Complex.ofReal_zero] at this
    rw [Fintype.sum_sum_type]
    refine Eq.trans ?_ this
    congr 1
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (fun i => by simp)
      (fun i => expPoly (half * conjPoly (A i)) (starRingEnd ℂ (rate i)) u)).symm
  have hP := eq_zero_of_sum_expPoly_eq_zero' hν P hsum (Sum.inl i)
  have hhalf : half ≠ 0 := by simp [half]
  refine ⟨fun hi => ?_, fun hi k => ?_⟩
  · simp only [P, Sum.elim_inl, hi, ↓reduceIte] at hP
    exact (mul_eq_zero.mp hP).resolve_left hhalf
  · have hnot : ¬ 0 < (rate i).im := by rw [hi]; exact lt_irrefl 0
    simp only [P, Sum.elim_inl, hnot, ↓reduceIte] at hP
    have h2 := congrArg (fun Q => (Q.coeff k).re) ((mul_eq_zero.mp hP).resolve_left hhalf)
    simp only [coeff_add, conjPoly, coeff_map, coeff_zero, Complex.add_re, Complex.conj_re,
      Complex.zero_re] at h2
    linarith

section Synthesis

open NNReal

variable {ι : Type*} [Fintype ι] (rate : ι → ℂ)

/-- Polynomial families with real coefficients at real rates. -/
def realCoefficientFamilies : Submodule ℝ (ι → ℂ[X]) where
  carrier := {P | ∀ i, (rate i).im = 0 → ∀ k, ((P i).coeff k).im = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ i hi k
    simp [hP i hi k, hQ i hi k]
  smul_mem' := by
    intro c P hP i hi k
    simp [coeff_smul, Complex.real_smul, hP i hi k]

/-- Synthesis of a real exponential polynomial from its polynomial coefficients. -/
noncomputable def realExpPolySynthesis :
    realCoefficientFamilies rate →ₗ[ℝ] (ℝ≥0 → ℝ) where
  toFun P u := ∑ i, (expPoly (P.1 i) (rate i) u).re
  map_add' P Q := by ext u; simp [expPoly_add, Finset.sum_add_distrib]
  map_smul' c P := by
    ext u
    simp [expPoly, eval_smul, Complex.real_smul, Finset.mul_sum, mul_assoc,
      mul_sub, Finset.sum_sub_distrib]

/-- Distinct rates in the closed upper half-plane uniquely determine their coefficients. -/
theorem realExpPolySynthesis_injective (hinj : Function.Injective rate)
    (hup : ∀ i, 0 ≤ (rate i).im) : Function.Injective (realExpPolySynthesis rate) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  have h : ∀ u : ℝ, 0 < u → ∑ i, (expPoly (P.1 i) (rate i) u).re = 0 :=
    fun u hu => congrFun hP ⟨u, hu.le⟩
  apply Subtype.ext
  funext i
  rcases (hup i).lt_or_eq with hi | hi
  · exact (eq_zero_of_sum_re_expPoly_eq_zero hinj hup P.1 h i).1 hi
  · ext k
    exact Complex.ext ((eq_zero_of_sum_re_expPoly_eq_zero hinj hup P.1 h i).2 hi.symm k)
      (P.2 i hi.symm k)

end Synthesis

end KernelRank
