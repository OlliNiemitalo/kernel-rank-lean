import KernelRankLean.Translations
import KernelRankLean.ProductRank
import KernelRankLean.RealExpPoly

/-!
# Sufficiency: a sum of components has separable rank equal to its cost

For a component with rate `λ` and polynomial `P` of degree `m - 1`, Taylor expansion gives
`P(u + t) exp (λ (u + t)) = ∑ k < m, (u ^ k exp (λ u)) · (Q k (t) exp (λ t))` with `Q k` the `k`-th
Hasse derivative of `P`, of degree `m - 1 - k`. Taking real parts,

  `Re (P(u + t) exp (λ (u + t))) = ∑ k, Re z k (u) · Re w k (t) - Im z k (u) · Im w k (t)`

with `z k (u) = u ^ k exp (λ u)` and `w k (t) = Q k (t) exp (λ t)`. For a real rate the imaginary
parts vanish. So the translates `u ↦ φ (u + t)` of a profile `φ` are sums of products of the
functions `Re z`, `Im z` of `u` and `Re w`, `- Im w` of `t`; both families are linearly
independent (the real parts of exponential polynomials vanish only trivially, and the `Q k` have
distinct degrees), so the translates span a space of dimension equal to the number of terms:
`m` per real rate and `2 m` per complex one.
-/

open Complex Polynomial NNReal

namespace KernelRank

/-! ### Exponential polynomials: linearity and Taylor expansion -/

lemma expPoly_sum {κ : Type*} (S : Finset κ) (Q : κ → ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (∑ k ∈ S, Q k) μ u = ∑ k ∈ S, expPoly (Q k) μ u := by
  simp [expPoly, eval_finsetSum, Finset.sum_mul]

lemma expPoly_X_pow (k : ℕ) (μ : ℂ) (u : ℝ) : expPoly (X ^ k) μ u = (u : ℂ) ^ k * exp (μ * u) := by
  simp [expPoly]

/-- For a real rate, `u ^ k exp (μ u)` is real. -/
lemma im_expPoly_X_pow {μ : ℂ} (hμ : μ.im = 0) (k : ℕ) (u : ℝ) : (expPoly (X ^ k) μ u).im = 0 := by
  have : μ = (μ.re : ℂ) := Complex.ext (by simp) (by simp [hμ])
  rw [expPoly_X_pow, this, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_im]

/-- Taylor expansion of a translated exponential polynomial. -/
lemma expPoly_translate {P : ℂ[X]} {m : ℕ} (hm : P.natDegree < m) (μ : ℂ) (u t : ℝ) :
    expPoly P μ (u + t) =
      ∑ k : Fin m, expPoly (X ^ (k : ℕ)) μ u * expPoly (hasseDeriv k P) μ t := by
  have htaylor : P.eval ((u : ℂ) + t) = ∑ k : Fin m, (hasseDeriv k P).eval (t : ℂ) * (u : ℂ) ^ (k : ℕ) := by
    rw [← taylor_eval, eval_eq_sum_range' (by rwa [natDegree_taylor]), ← Fin.sum_univ_eq_sum_range]
    simp [taylor_coeff]
  simp only [expPoly, Complex.ofReal_add, htaylor, eval_pow, eval_X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, Complex.exp_add]
  ring

/-! ### The triangular family of Hasse derivatives -/

/-- The Hasse derivatives `hasseDeriv k P`, `k ≤ deg P`, have degrees `deg P - k`, so a vanishing
combination of them is trivial. -/
lemma eq_zero_of_sum_hasseDeriv_eq_zero {P : ℂ[X]} (hP : P ≠ 0) (c : Fin (P.natDegree + 1) → ℂ)
    (h : ∑ k, C (c k) * hasseDeriv k P = 0) : ∀ k, c k = 0 := by
  classical
  by_contra hne
  obtain ⟨k₀, hk₀, hmin'⟩ :=
    wellFounded_lt.has_min {k | c k ≠ 0} (by simpa [Set.Nonempty] using not_forall.mp hne)
  have hmin : ∀ k, k < k₀ → c k = 0 := fun k hk => by
    by_contra hck
    exact hmin' k hck hk
  have hcoeff := congrArg (fun Q => Q.coeff (P.natDegree - k₀)) h
  simp only [finsetSum_coeff, coeff_C_mul, hasseDeriv_coeff, coeff_zero] at hcoeff
  have hk : P.natDegree - (k₀ : ℕ) + k₀ = P.natDegree :=
    Nat.sub_add_cancel (Nat.lt_succ_iff.mp k₀.2)
  rw [Finset.sum_eq_single k₀] at hcoeff
  · rw [hk, ← leadingCoeff] at hcoeff
    have hchoose : ((P.natDegree.choose k₀ : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.lt_succ_iff.mp k₀.2)).ne'
    exact mul_ne_zero hk₀ (mul_ne_zero hchoose (leadingCoeff_ne_zero.mpr hP)) hcoeff
  · intro k _ hk'
    rcases lt_or_gt_of_ne hk' with hlt | hgt
    · simp [hmin k hlt]
    · have hk₀k : (k₀ : ℕ) < k := hgt
      have hdeg : P.natDegree < P.natDegree - k₀ + k := by have := k₀.2; omega
      rw [coeff_eq_zero_of_natDegree_lt hdeg]
      simp
  · simp

/-! ### A family of components -/

section Family

open scoped Classical

variable {ι : Type*} [Fintype ι] (comp : ι → Component)

/-- The profile of a family of components. -/
noncomputable def familyProfile (s : ℝ) : ℝ :=
  ∑ i, (comp i).eval s

/-- The rendering terms of a family: `m × 2` for each complex rate, `m` for each real one. -/
abbrev TermIndex :=
  (Σ i : {i // (comp i).rate.im ≠ 0}, Fin (comp i).multiplicity × Fin 2) ⊕
    (Σ i : {i // (comp i).rate.im = 0}, Fin (comp i).multiplicity)

/-- `z i k u = u ^ k exp (λ u)`: the functions of `u`. -/
noncomputable def zFun (i : ι) (k : ℕ) (u : ℝ) : ℂ := expPoly (X ^ k) (comp i).rate u

/-- `w i k t = Q k (t) exp (λ t)` with `Q k` the `k`-th Hasse derivative: the functions of `t`. -/
noncomputable def wFun (i : ι) (k : ℕ) (t : ℝ) : ℂ := expPoly (hasseDeriv k (comp i).poly) (comp i).rate t

/-- The rendering terms' functions of `u`: `Re z`, `Im z` for complex rates, `Re z` for real ones. -/
noncomputable def uFactor : TermIndex comp → ℝ≥0 → ℝ :=
  Sum.elim (fun j u => if j.2.2 = 0 then (zFun comp j.1 j.2.1 u).re else (zFun comp j.1 j.2.1 u).im)
    (fun j u => (zFun comp j.1 j.2 u).re)

/-- The rendering terms' functions of `t`: `Re w`, `- Im w` for complex rates, `Re w` for real
ones. -/
noncomputable def tFactor : TermIndex comp → ℝ≥0 → ℝ :=
  Sum.elim (fun j t => if j.2.2 = 0 then (wFun comp j.1 j.2.1 t).re else -(wFun comp j.1 j.2.1 t).im)
    (fun j t => (wFun comp j.1 j.2 t).re)

omit [Fintype ι] in
/-- A component's translate as a sum of products. -/
theorem eval_translate (i : ι) (u t : ℝ) :
    (comp i).eval (u + t) = ∑ k : Fin (comp i).multiplicity,
      ((zFun comp i k u).re * (wFun comp i k t).re - (zFun comp i k u).im * (wFun comp i k t).im) := by
  change (expPoly (comp i).poly (comp i).rate (u + t)).re = _
  rw [expPoly_translate (Nat.lt_succ_self _), Complex.re_sum]
  rfl

/-- The translates of a family's profile are sums of products of the two factor families. -/
lemma familyProfile_translate (t : ℝ≥0) :
    (fun u : ℝ≥0 => familyProfile comp (u + t)) = ∑ j, tFactor comp j t • uFactor comp j := by
  funext u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, familyProfile]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => (comp i).rate.im = 0), add_comm,
    Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_translate, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Fin.sum_univ_two, tFactor, uFactor]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_translate]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [tFactor, uFactor, Sum.elim_inr, zFun, im_expPoly_X_pow i.2, zero_mul, sub_zero]
    ring

lemma coeff_sum_C_mul_X_pow {m : ℕ} (c : Fin m → ℂ) (k : Fin m) :
    (∑ k', C (c k') * X ^ (k' : ℕ)).coeff k = c k := by
  simp [finsetSum_coeff, Fin.val_inj]

variable {comp}

/-- The functions `Re z`, `Im z` of `u` are linearly independent. -/
lemma linearIndependent_uFactor (hinj : Function.Injective fun i => (comp i).rate)
    (hup : ∀ i, 0 ≤ (comp i).rate.im) : LinearIndependent ℝ (uFactor comp) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Each component's coefficients, combined into one complex polynomial.
  let c : ∀ i, Fin (comp i).multiplicity → ℂ := fun i k =>
    if h : (comp i).rate.im = 0 then (g (Sum.inr ⟨⟨i, h⟩, k⟩) : ℂ)
    else (g (Sum.inl ⟨⟨i, h⟩, k, 0⟩) : ℂ) - I * g (Sum.inl ⟨⟨i, h⟩, k, 1⟩)
  let A : ι → ℂ[X] := fun i => ∑ k, C (c i k) * X ^ (k : ℕ)
  have hA : ∀ u : ℝ, 0 < u → ∑ i, (expPoly (A i) (comp i).rate u).re = 0 := by
    intro u hu
    have := congrFun hg ⟨u, hu.le⟩
    erw [Finset.sum_apply] at this
    replace this : ∑ j, g j * uFactor comp j ⟨u, hu.le⟩ = 0 := this
    rw [← this,  Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma,
      ← Fintype.sum_subtype_add_sum_subtype (fun i => (comp i).rate.im = 0), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      simp only [A, expPoly_sum, expPoly_C_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [c, i.2, Fin.sum_univ_two, uFactor, zFun, Complex.mul_re]
      rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [A, expPoly_sum, expPoly_C_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [c, i.2, uFactor, zFun]
      exact Or.inl rfl
  rintro (⟨⟨i, hi⟩, k, p⟩ | ⟨⟨i, hi⟩, k⟩)
  · have hpos : 0 < (comp i).rate.im := lt_of_le_of_ne (hup i) (Ne.symm hi)
    have hc := congrArg (fun P => P.coeff k)
      ((eq_zero_of_sum_re_expPoly_eq_zero hinj hup A hA i).1 hpos)
    simp only [A, coeff_sum_C_mul_X_pow, coeff_zero] at hc
    simp only [c, hi, ↓reduceDIte] at hc
    have hre := congrArg Complex.re hc
    have him := congrArg Complex.im hc
    simp at hre him
    fin_cases p
    · exact hre
    · exact him
  · have hc := (eq_zero_of_sum_re_expPoly_eq_zero hinj hup A hA i).2 hi k
    simp only [A, coeff_sum_C_mul_X_pow] at hc
    simpa [c, hi] using hc

/-- The functions `Re w`, `- Im w` of `t` are linearly independent. -/
lemma linearIndependent_tFactor (hinj : Function.Injective fun i => (comp i).rate)
    (hwf : ∀ i, (comp i).WellFormed) : LinearIndependent ℝ (tFactor comp) := by
  have hup : ∀ i, 0 ≤ (comp i).rate.im := fun i => (hwf i).2.1
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Each component's coefficients, combined with its Hasse derivatives into one polynomial.
  let c : ∀ i, Fin (comp i).multiplicity → ℂ := fun i k =>
    if h : (comp i).rate.im = 0 then (g (Sum.inr ⟨⟨i, h⟩, k⟩) : ℂ)
    else (g (Sum.inl ⟨⟨i, h⟩, k, 0⟩) : ℂ) + I * g (Sum.inl ⟨⟨i, h⟩, k, 1⟩)
  let B : ι → ℂ[X] := fun i => ∑ k, C (c i k) * hasseDeriv k (comp i).poly
  have hB : ∀ t : ℝ, 0 < t → ∑ i, (expPoly (B i) (comp i).rate t).re = 0 := by
    intro t ht
    have := congrFun hg t.toNNReal
    erw [Finset.sum_apply] at this
    replace this : ∑ j, g j * tFactor comp j t.toNNReal = 0 := this
    have ht' : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
    rw [← this, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma,
      ← Fintype.sum_subtype_add_sum_subtype (fun i => (comp i).rate.im = 0), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      simp only [B, expPoly_sum, expPoly_C_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [c, i.2, Fin.sum_univ_two, tFactor, wFun, Complex.mul_re, ht']
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [B, expPoly_sum, expPoly_C_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [c, i.2, tFactor, wFun, ht']
  -- Each `B i` vanishes: directly for a complex rate; for a real rate its coefficients are real.
  have hB0 : ∀ i, B i = 0 := by
    intro i
    rcases (hup i).lt_or_eq with hpos | hzero
    · exact (eq_zero_of_sum_re_expPoly_eq_zero hinj hup B hB i).1 hpos
    · have hre := (eq_zero_of_sum_re_expPoly_eq_zero hinj hup B hB i).2 hzero.symm
      ext n
      apply Complex.ext
      · simpa using hre n
      · simp only [B, finsetSum_coeff, coeff_C_mul, hasseDeriv_coeff, Complex.im_sum,
          coeff_zero, Complex.zero_im]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [c, hzero.symm, (hwf i).2.2 hzero.symm]
  rintro (⟨⟨i, hi⟩, k, p⟩ | ⟨⟨i, hi⟩, k⟩)
  · have hc := eq_zero_of_sum_hasseDeriv_eq_zero (hwf i).1 (c i) (hB0 i) k
    simp only [c, hi, ↓reduceDIte] at hc
    have hre := congrArg Complex.re hc
    have him := congrArg Complex.im hc
    simp at hre him
    fin_cases p
    · exact hre
    · exact him
  · have hc := eq_zero_of_sum_hasseDeriv_eq_zero (hwf i).1 (c i) (hB0 i) k
    simpa [c, hi] using hc

/-- The number of rendering terms of a family is its total cost. -/
lemma card_termIndex : Fintype.card (TermIndex comp) = ∑ i, (comp i).cost := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => (comp i).rate.im = 0), add_comm]
  simp only [TermIndex, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [Component.cost, i.2, mul_comm]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [Component.cost, i.2]

/-- The translates of a well-formed family's profile, with distinct rates, span a space of
dimension equal to the family's total cost. -/
theorem finrank_translateSpan_familyProfile (hinj : Function.Injective fun i => (comp i).rate)
    (hwf : ∀ i, (comp i).WellFormed) :
    FiniteDimensional ℝ (translateSpan (familyProfile comp)) ∧
      Module.finrank ℝ (translateSpan (familyProfile comp)) = ∑ i, (comp i).cost := by
  have hG : ∀ t : ℝ≥0, (fun u : ℝ≥0 => familyProfile comp (u + t)) =
      ∑ j, tFactor comp j t • uFactor comp j := familyProfile_translate comp
  have hspan := span_range_eq_of_linearIndependent_coefficients (uFactor comp)
    (linearIndependent_tFactor hinj hwf) hG
  refine ⟨?_, ?_⟩
  · unfold translateSpan
    rw [hspan]
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  · unfold translateSpan
    rw [finrank_span_range_eq_card (linearIndependent_uFactor hinj fun i => (hwf i).2.1)
      (linearIndependent_tFactor hinj hwf) hG, card_termIndex]

end Family

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
