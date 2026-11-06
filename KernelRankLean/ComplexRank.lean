import KernelRankLean.Translations
import KernelRankLean.ProductRank
import KernelRankLean.RealExpPoly

/-!
# Exact rank of complex exponential polynomials

For distinct rates and nonzero polynomials, the translates of `∑ i, P i(t) exp (rate i * t)`
span a complex vector space of dimension `∑ i, (P i).natDegree + 1`. Taylor expansion gives
two independent factor families: the monomials and the Hasse derivatives, synthesized at their
respective rates. No reality or conjugation conditions are needed.
-/

open Complex Polynomial NNReal

namespace KernelRank

lemma expPoly_sum {κ : Type*} (S : Finset κ) (Q : κ → ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (∑ k ∈ S, Q k) μ u = ∑ k ∈ S, expPoly (Q k) μ u := by
  simp [expPoly, eval_finsetSum, Finset.sum_mul]

/-- Taylor expansion of a translated exponential polynomial. -/
lemma expPoly_translate {P : ℂ[X]} {m : ℕ} (hm : P.natDegree < m) (μ : ℂ) (u t : ℝ) :
    expPoly P μ (u + t) =
      ∑ k : Fin m, expPoly (X ^ (k : ℕ)) μ u * expPoly (hasseDeriv k P) μ t := by
  have htaylor : P.eval ((u : ℂ) + t) =
      ∑ k : Fin m, (hasseDeriv k P).eval (t : ℂ) * (u : ℂ) ^ (k : ℕ) := by
    rw [← taylor_eval, eval_eq_sum_range' (by rwa [natDegree_taylor]),
      ← Fin.sum_univ_eq_sum_range]
    simp [taylor_coeff]
  simp only [expPoly, Complex.ofReal_add, htaylor, eval_pow, eval_X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, Complex.exp_add]
  ring

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

/-- Synthesis at distinct rates preserves independence of complex polynomial families. -/
lemma linearIndependent_expPoly {ι : Type*} [Finite ι] {κ : ι → Type*}
    [∀ i, Finite (κ i)] {rate : ι → ℂ} (hinj : Function.Injective rate)
    (Q : ∀ i, κ i → ℂ[X]) (hQ : ∀ i, LinearIndependent ℂ (Q i)) :
    LinearIndependent ℂ (fun j : Σ i, κ i => fun u : ℝ≥0 => expPoly (Q j.1 j.2) (rate j.1) u) := by
  classical
  let := Fintype.ofFinite ι
  let (i : ι) := Fintype.ofFinite (κ i)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let A (i : ι) : ℂ[X] := ∑ k, c ⟨i, k⟩ • Q i k
  have hA : ∀ u : ℝ, 0 < u → ∑ i, expPoly (A i) (rate i) u = 0 := by
    intro u hu
    have := congrFun hc ⟨u, hu.le⟩
    erw [Finset.sum_apply] at this
    replace this : ∑ j : Σ i, κ i, c j * expPoly (Q j.1 j.2) (rate j.1) u = 0 := this
    simpa only [A, smul_eq_C_mul, expPoly_sum, expPoly_C_mul, Fintype.sum_sigma] using this
  rintro ⟨i, k⟩
  exact Fintype.linearIndependent_iff.mp (hQ i) (fun k => c ⟨i, k⟩)
    (eq_zero_of_sum_expPoly_eq_zero' hinj A hA i) k

/-- The dimension of a complex exponential polynomial's translate span is its total multiplicity. -/
theorem finrank_translateSpan_sum_expPoly {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    FiniteDimensional ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) ∧
      Module.finrank ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) =
        ∑ i, ((P i).natDegree + 1) := by
  classical
  let f (j : Σ i, Fin ((P i).natDegree + 1)) (u : ℝ≥0) :=
    expPoly (X ^ (j.2 : ℕ)) (rate j.1) u
  let a (j : Σ i, Fin ((P i).natDegree + 1)) (t : ℝ≥0) :=
    expPoly (hasseDeriv j.2 (P j.1)) (rate j.1) t
  have hmono (i : ι) :
      LinearIndependent ℂ (fun k : Fin ((P i).natDegree + 1) => (X : ℂ[X]) ^ (k : ℕ)) := by
    simpa only [Function.comp_def, Submodule.subtype_apply, degreeLT.basis_val] using
      (degreeLT.basis ℂ ((P i).natDegree + 1)).linearIndependent.map'
        (degreeLT ℂ ((P i).natDegree + 1)).subtype (by simp)
  have hf : LinearIndependent ℂ f :=
    linearIndependent_expPoly hinj (fun i (k : Fin ((P i).natDegree + 1)) => X ^ (k : ℕ)) hmono
  have ha : LinearIndependent ℂ a :=
    linearIndependent_expPoly hinj
      (fun i (k : Fin ((P i).natDegree + 1)) => hasseDeriv k (P i))
      (fun i => linearIndependent_hasseDeriv (hP i))
  have hG (t : ℝ≥0) :
      (fun u : ℝ≥0 => ∑ i, expPoly (P i) (rate i) (u + t)) = ∑ j, a j t • f j := by
    ext u
    simp only [f, a, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun i _ => by
      rw [expPoly_translate (Nat.lt_succ_self _)]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hspan := span_range_eq_of_linearIndependent_coefficients f ha hG
  refine ⟨?_, ?_⟩
  · unfold translateSpan
    rw [hspan]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  · unfold translateSpan
    rw [finrank_span_range_eq_card hf ha hG]
    simp only [Fintype.card_sigma, Fintype.card_fin]

/-- Exact separable rank of the Hankel kernel of a complex exponential polynomial. -/
theorem separableRank_sum_expPoly {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    separableRank (fun s t : ℝ≥0 => ∑ i, expPoly (P i) (rate i) (s + t)) =
      (∑ i, ((P i).natDegree + 1) : ℕ) := by
  obtain ⟨hfin, hdim⟩ := finrank_translateSpan_sum_expPoly hinj P hP
  let : FiniteDimensional ℂ
      (rowSpan (fun s t : ℝ≥0 => ∑ i, expPoly (P i) (rate i) (s + t))) := hfin
  rw [separableRank_eq_finrank_rowSpan]
  exact_mod_cast hdim

end KernelRank
