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
independent: the injective coefficient synthesis map transports independence of the monomials and
of the Hasse derivatives (which have distinct degrees). Thus the translates span a space of
dimension equal to the number of terms:
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

/-- The Hasse derivatives of a nonzero polynomial are independent: their degrees are distinct. -/
lemma linearIndependent_hasseDeriv {P : ℂ[X]} (hP : P ≠ 0) :
    LinearIndependent ℂ (fun k : Fin (P.natDegree + 1) => hasseDeriv k P) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c h
  simp only [smul_eq_C_mul] at h
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

variable {comp}

/-- Real and scaled imaginary parts of a family of exponential polynomials. -/
noncomputable def expPolyFactors (Q : ∀ i, Fin (comp i).multiplicity → ℂ[X]) (σ : ℝ) :
    TermIndex comp → ℝ≥0 → ℝ :=
  Sum.elim (fun j u => if j.2.2 = 0 then (expPoly (Q j.1 j.2.1) (comp j.1).rate u).re
    else σ * (expPoly (Q j.1 j.2.1) (comp j.1).rate u).im)
    (fun j u => (expPoly (Q j.1 j.2) (comp j.1).rate u).re)

omit [Fintype ι] in
/-- Injective synthesis transports independence of polynomial families to their real factors. -/
lemma linearIndependent_expPolyFactors [Finite ι]
    (hinj : Function.Injective fun i => (comp i).rate)
    (hup : ∀ i, 0 ≤ (comp i).rate.im)
    (Q : ∀ i, Fin (comp i).multiplicity → ℂ[X])
    (hQ : ∀ i, LinearIndependent ℂ (Q i))
    (hreal : ∀ i, (comp i).rate.im = 0 → ∀ k n, ((Q i k).coeff n).im = 0)
    (σ : ℝ) (hσ : σ ≠ 0) : LinearIndependent ℝ (expPolyFactors Q σ) := by
  letI := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let c : ∀ i, Fin (comp i).multiplicity → ℂ := fun i k =>
    if h : (comp i).rate.im = 0 then (g (Sum.inr ⟨⟨i, h⟩, k⟩) : ℂ)
    else (g (Sum.inl ⟨⟨i, h⟩, k, 0⟩) : ℂ) -
      I * (σ * g (Sum.inl ⟨⟨i, h⟩, k, 1⟩) : ℝ)
  let A : ι → ℂ[X] := fun i => ∑ k, C (c i k) * Q i k
  have hAr : A ∈ realCoefficientFamilies (fun i => (comp i).rate) := by
    intro i hi n
    simp only [A, finsetSum_coeff, coeff_C_mul, Complex.im_sum]
    exact Finset.sum_eq_zero fun k _ => by simp [c, hi, Complex.mul_im, hreal i hi k n]
  have hA : realExpPolySynthesis (fun i => (comp i).rate) ⟨A, hAr⟩ = 0 := by
    ext u
    change ∑ i, (expPoly (A i) (comp i).rate u).re = 0
    have := congrFun hg u
    erw [Finset.sum_apply] at this
    replace this : ∑ j, g j * expPolyFactors Q σ j u = 0 := this
    rw [← this, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma,
      ← Fintype.sum_subtype_add_sum_subtype (fun i => (comp i).rate.im = 0), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      simp only [A, expPoly_sum, expPoly_C_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [c, i.2, Fin.sum_univ_two, expPolyFactors, Complex.mul_re]
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [A, expPoly_sum, expPoly_C_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [c, i.2, expPolyFactors]
  have hA0 : (⟨A, hAr⟩ : realCoefficientFamilies (fun i => (comp i).rate)) = 0 :=
    realExpPolySynthesis_injective _ hinj hup (hA.trans (map_zero _).symm)
  have hc : ∀ i k, c i k = 0 := fun i =>
    Fintype.linearIndependent_iff.mp (hQ i) (c i)
      (by simpa only [A, smul_eq_C_mul, Submodule.coe_zero, Pi.zero_apply] using
        congrFun (congrArg Subtype.val hA0) i)
  rintro (⟨⟨i, hi⟩, k, p⟩ | ⟨⟨i, hi⟩, k⟩)
  · fin_cases p
    · simpa [c, hi] using congrArg Complex.re (hc i k)
    · simpa [c, hi, mul_eq_zero, hσ] using congrArg Complex.im (hc i k)
  · simpa [c, hi] using hc i k

/-- The functions `Re z`, `Im z` of `u` are linearly independent. -/
lemma linearIndependent_uFactor (hinj : Function.Injective fun i => (comp i).rate)
    (hup : ∀ i, 0 ≤ (comp i).rate.im) : LinearIndependent ℝ (uFactor comp) := by
  have hQ (i : ι) :
      LinearIndependent ℂ (fun k : Fin (comp i).multiplicity => (X : ℂ[X]) ^ (k : ℕ)) := by
    simpa only [Function.comp_def, Submodule.subtype_apply, degreeLT.basis_val] using
      (degreeLT.basis ℂ (comp i).multiplicity).linearIndependent.map'
        (degreeLT ℂ (comp i).multiplicity).subtype (by simp)
  simpa only [expPolyFactors, uFactor, zFun, one_mul] using
    linearIndependent_expPolyFactors hinj hup _ hQ
      (fun _ _ _ _ => by simp [apply_ite]) 1 one_ne_zero

/-- The functions `Re w`, `- Im w` of `t` are linearly independent. -/
lemma linearIndependent_tFactor (hinj : Function.Injective fun i => (comp i).rate)
    (hwf : ∀ i, (comp i).WellFormed) : LinearIndependent ℝ (tFactor comp) := by
  have hQ (i : ι) :
      LinearIndependent ℂ (fun k : Fin (comp i).multiplicity => hasseDeriv k (comp i).poly) := by
    exact linearIndependent_hasseDeriv (hwf i).1
  simpa only [expPolyFactors, tFactor, wFun, neg_one_mul] using
    linearIndependent_expPolyFactors hinj (fun i => (hwf i).2.1) _ hQ
      (fun i hi k n => by simp [hasseDeriv_coeff, (hwf i).2.2 hi]) (-1) (by norm_num)

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
