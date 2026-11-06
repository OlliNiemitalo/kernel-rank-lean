import KernelRankLean.Differential
import KernelRankLean.RealExpPoly

/-!
# Exact rank of complex exponential polynomials

For distinct rates and nonzero polynomials, the translates of `∑ i, P i(t) exp (rate i * t)`
span a complex vector space of dimension `∑ i, (P i).natDegree + 1`. Taylor expansion gives the
upper bound. The differential annihilator is the product of rate factors to their multiplicities;
Cayley–Hamilton gives the lower bound. No reality or conjugation conditions are needed.
-/

open Complex Polynomial NNReal

namespace KernelRank

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

lemma aeval_derivative_apply (q P : ℂ[X]) :
    aeval (derivative : Module.End ℂ ℂ[X]) q P =
      ∑ k : Fin (P.natDegree + 1),
        (q.coeff k * (k.val.factorial : ℂ)) • hasseDeriv k P := by
  let N := max (q.natDegree + 1) (P.natDegree + 1)
  have hpow (k : ℕ) :
      ((derivative : Module.End ℂ ℂ[X]) ^ k) P =
        (k.factorial : ℂ) • hasseDeriv k P := by
    rw [Module.End.pow_apply, ← factorial_smul_hasseDeriv]
    simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  rw [aeval_eq_sum_range'
    (show q.natDegree < N from lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)) derivative]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hpow, smul_smul]
  change ∑ k ∈ Finset.range N, (q.coeff k * (k.factorial : ℂ)) • hasseDeriv k P =
    ∑ k : Fin (P.natDegree + 1),
      (fun k : ℕ => (q.coeff k * (k.factorial : ℂ)) • hasseDeriv k P) k
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (q.coeff k * (k.factorial : ℂ)) • hasseDeriv k P) (P.natDegree + 1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.le_max_right ..))
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [hasseDeriv_eq_zero_of_lt_natDegree P k (by omega), smul_zero]

lemma aeval_derivative_eq_zero_iff (q : ℂ[X]) {P : ℂ[X]} (hP : P ≠ 0) :
    aeval (derivative : Module.End ℂ ℂ[X]) q P = 0 ↔
      X ^ (P.natDegree + 1) ∣ q := by
  rw [aeval_derivative_apply, X_pow_dvd_iff]
  constructor
  · intro h k hk
    have hc := Fintype.linearIndependent_iff.mp (linearIndependent_hasseDeriv hP) _ h ⟨k, hk⟩
    exact (mul_eq_zero.mp hc).resolve_right (by exact_mod_cast k.factorial_ne_zero)
  · intro h
    exact Finset.sum_eq_zero fun k _ => by rw [h k k.2, zero_mul, zero_smul]

lemma aeval_shifted_derivative_eq_zero_iff (q : ℂ[X]) {P : ℂ[X]} (hP : P ≠ 0) (μ : ℂ) :
    aeval ((derivative : Module.End ℂ ℂ[X]) + μ • 1) q P = 0 ↔
      (X - C μ) ^ (P.natDegree + 1) ∣ q := by
  have hshift :
      aeval ((derivative : Module.End ℂ ℂ[X]) + μ • 1) q =
        aeval (derivative : Module.End ℂ ℂ[X]) (taylor μ q) := by
    rw [taylor_apply, aeval_comp]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hshift, aeval_derivative_eq_zero_iff _ hP]
  constructor
  · intro h
    have h' := (taylorAlgHom (-μ)).map_dvd h
    change taylor (-μ) (X ^ (P.natDegree + 1)) ∣ taylor (-μ) (taylor μ q) at h'
    rw [taylor_taylor] at h'
    simpa [taylor_taylor, taylor_apply, sub_eq_add_neg] using h'
  · intro h
    have h' := (taylorAlgHom μ).map_dvd h
    simpa [taylor_apply] using h'

lemma iteratedDerivWithin_sum_expPoly {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin k (fun u => ∑ i, expPoly (P i) (rate i) u) (Set.Ici 0) t =
      ∑ i, expPoly ((((derivative : Module.End ℂ ℂ[X]) + rate i • 1) ^ k) (P i)) (rate i) t := by
  induction k generalizing t with
  | zero => simp [iteratedDerivWithin_zero]
  | succ k ih =>
    rw [iteratedDerivWithin_succ]
    have heq : Set.EqOn
        (iteratedDerivWithin k (fun u => ∑ i, expPoly (P i) (rate i) u) (Set.Ici 0))
        (fun u => ∑ i, expPoly
          ((((derivative : Module.End ℂ ℂ[X]) + rate i • 1) ^ k) (P i)) (rate i) u)
        (Set.Ici 0) := fun u hu => ih hu
    rw [derivWithin_congr heq (heq ht),
      (HasDerivAt.fun_sum fun i _ => hasDerivAt_expPoly
        ((((derivative : Module.End ℂ ℂ[X]) + rate i • 1) ^ k) (P i))
        (rate i) t).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)]
    simp only [pow_succ', Module.End.mul_apply]
    simp [smul_eq_C_mul]

lemma differentialOperator_sum_expPoly {ι : Type*} [Fintype ι]
    (q : ℂ[X]) (P : ι → ℂ[X]) (rate : ι → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator q (fun u => ∑ i, expPoly (P i) (rate i) u) t =
      ∑ i, expPoly (aeval ((derivative : Module.End ℂ ℂ[X]) + rate i • 1) q (P i)) (rate i) t := by
  simp only [differentialOperator, iteratedDerivWithin_sum_expPoly P rate _ ht, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [aeval_eq_sum_range, expPoly, eval_finsetSum, Finset.sum_mul, smul_eq_C_mul, mul_assoc]

/-- The rate factors, each raised to its polynomial multiplicity. -/
noncomputable def expPolyAnnihilator {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) : ℂ[X] :=
  ∏ i, (X - C (rate i)) ^ ((P i).natDegree + 1)

lemma expPolyAnnihilator_monic {ι : Type*} [Fintype ι] (P : ι → ℂ[X]) (rate : ι → ℂ) :
    (expPolyAnnihilator P rate).Monic :=
  monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C (rate i)).pow _

lemma expPolyAnnihilator_natDegree {ι : Type*} [Fintype ι] (P : ι → ℂ[X]) (rate : ι → ℂ) :
    (expPolyAnnihilator P rate).natDegree = ∑ i, ((P i).natDegree + 1) := by
  rw [expPolyAnnihilator, natDegree_prod_of_monic _ _
    (fun i _ => (monic_X_sub_C (rate i)).pow _)]
  simp

/-- A differential polynomial annihilates the sum exactly when all rate factors divide it. -/
lemma differentialOperator_sum_expPoly_eq_zero_iff {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) (hinj : Function.Injective rate)
    (hP : ∀ i, P i ≠ 0) (q : ℂ[X]) :
    (∀ t, 0 ≤ t → differentialOperator q (fun u => ∑ i, expPoly (P i) (rate i) u) t = 0) ↔
      expPolyAnnihilator P rate ∣ q := by
  constructor
  · intro h
    change (∏ i, (X - C (rate i)) ^ ((P i).natDegree + 1)) ∣ q
    apply Fintype.prod_dvd_of_coprime
      (fun i j hij => (pairwise_coprime_X_sub_C hinj hij).pow)
    intro i
    apply (aeval_shifted_derivative_eq_zero_iff q (hP i) (rate i)).mp
    exact eq_zero_of_sum_expPoly_eq_zero' hinj _ (fun t ht => by
      rw [← differentialOperator_sum_expPoly q P rate ht.le]
      exact h t ht.le) i
  · intro h t ht
    rw [differentialOperator_sum_expPoly q P rate ht]
    apply Finset.sum_eq_zero
    intro i _
    have hi' : (X - C (rate i)) ^ ((P i).natDegree + 1) ∣ expPolyAnnihilator P rate :=
      Finset.dvd_prod_of_mem
        (fun j : ι => (X - C (rate j)) ^ ((P j).natDegree + 1)) (Finset.mem_univ i)
    have hi := dvd_trans hi' h
    rw [(aeval_shifted_derivative_eq_zero_iff q (hP i) (rate i)).mpr hi, expPoly_zero]

/-- The dimension of a complex exponential polynomial's translate span is its total multiplicity. -/
theorem finrank_translateSpan_sum_expPoly {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    FiniteDimensional ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) ∧
      Module.finrank ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) =
        ∑ i, ((P i).natDegree + 1) := by
  classical
  let ψ := fun t => ∑ i, expPoly (P i) (rate i) t
  let f (j : Σ i, Fin ((P i).natDegree + 1)) (u : ℝ≥0) :=
    expPoly (X ^ (j.2 : ℕ)) (rate j.1) u
  have hG (t : ℝ≥0) :
      (fun u : ℝ≥0 => ψ (u + t)) =
        ∑ j, expPoly (hasseDeriv j.2 (P j.1)) (rate j.1) t • f j := by
    ext u
    simp only [f, ψ, Finset.sum_apply, smul_eq_mul, Pi.smul_apply, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun i _ => by
      rw [expPoly_translate (Nat.lt_succ_self _)]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hspan : translateSpan ψ ≤ Submodule.span ℂ (Set.range f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    change (fun u : ℝ≥0 => ψ (u + t)) ∈ Submodule.span ℂ (Set.range f)
    rw [hG t]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  have hfin := Submodule.finiteDimensional_of_le hspan
  let : FiniteDimensional ℂ (translateSpan ψ) := hfin
  have hcont : Continuous ψ := by
    dsimp [ψ, expPoly]
    fun_prop
  obtain ⟨q, hq, hdeg, hann⟩ := exists_charpoly_differential_annihilator ψ hcont.continuousOn
  refine ⟨hfin, le_antisymm ?_ ?_⟩
  · calc
      Module.finrank ℂ (translateSpan ψ) ≤
          Module.finrank ℂ (Submodule.span ℂ (Set.range f)) := Submodule.finrank_mono hspan
      _ ≤ Fintype.card (Σ i, Fin ((P i).natDegree + 1)) := finrank_range_le_card f
      _ = _ := by simp
  · rw [← hdeg, ← expPolyAnnihilator_natDegree P rate]
    exact natDegree_le_of_dvd
      ((differentialOperator_sum_expPoly_eq_zero_iff P rate hinj hP q).mp hann) hq.ne_zero

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
