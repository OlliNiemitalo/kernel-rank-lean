import KernelRankLean.ComplexRank

/-!
# Exact `d`-way rank of complex exponential polynomials

In `d ≥ 2` coordinates, for distinct complex rates and nonzero polynomials `P i`, the `d`-way
Hankel kernel `s ↦ ∑ i, P i (∑ j, s j) · exp (rate i · ∑ j, s j)` on `[0, ∞)^d`—and hence the
radial kernel `x ↦ ∑ i, P i (∑ j, x j ^ 2) · exp (rate i · ∑ j, x j ^ 2)` on `ℝ^d`—has exact
complex separable rank `∑ i, ((d - 1) * (P i).natDegree + 1)`.

* **Upper bound.** For a single term of degree `k`, multiply the reversed Hasse-derivative
  polynomial in `z` on coordinate `0` by `d - 1` truncated exponential polynomials of degree `k`
  on the remaining coordinates. Their product in `ℂ[X]` has degree at most `d k`, and its `z ^ k`
  coefficient is `P (∑ j, s j)`. Averaging over `L = (d - 1) k + 1` roots of unity extracts that
  coefficient with no wraparound, since `d k < k + L`.
* **Lower bound.** Exponential-monomial independence turns any `R`-term decomposition into a
  decomposition of a `d`-multilinear form into products of linear functionals. An Alder–Strassen
  peeling induction removes `d - 1` terms per degree step (using `Fin` shifts in the last
  coordinate) and `1` term for each constant block.
-/

open Complex Polynomial NNReal

namespace KernelRank

/-! ### Root-of-unity upper bound -/

/-- Extracting the `k`-th coefficient of a polynomial `Q ∈ ℂ[X]` of degree `< k + L` (with
`k < L`) by averaging `ζ ^ (-k r) · Q(ζ ^ r)` over the `L`-th roots of unity. -/
lemma coeff_eq_sum_rootsOfUnity (Q : ℂ[X]) {k L : ℕ} (hkL : k < L)
    (hdeg : Q.natDegree < k + L) :
    Q.coeff k = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L,
      exp (-2 * Real.pi * I * k * r / L) * Q.eval (exp (2 * Real.pi * I * r / L)) := by
  have hL : (0 : ℕ) < L := Nat.zero_lt_of_lt hkL
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have heval (r : ℕ) : Q.eval (exp (2 * Real.pi * I * r / L)) =
      ∑ n ∈ Finset.range (k + L), Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n :=
    eval_eq_sum_range' hdeg _
  simp_rw [heval]
  have hswap : (∑ r ∈ Finset.range L,
      exp (-2 * Real.pi * I * k * r / L) *
        ∑ n ∈ Finset.range (k + L), Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n) =
      ∑ n ∈ Finset.range (k + L), ∑ r ∈ Finset.range L,
        exp (-2 * Real.pi * I * k * r / L) *
          (Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  have hinner (n : ℕ) (hn : n ∈ Finset.range (k + L)) :
      (∑ r ∈ Finset.range L,
        exp (-2 * Real.pi * I * k * r / L) *
          (Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n)) =
        if n = k then (L : ℂ) * Q.coeff k else 0 := by
    let w : ℂ := exp (2 * Real.pi * I * ((n : ℤ) - k) / L)
    have hterm (r : ℕ) :
        exp (-2 * Real.pi * I * k * r / L) * (Q.coeff n * exp (2 * Real.pi * I * r / L) ^ n) =
          Q.coeff n * w ^ r := by
      rw [← mul_left_comm (Q.coeff n)]
      congr 1
      rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    split_ifs with hnk
    · subst hnk
      simp [w, mul_comm]
    · suffices ∑ r ∈ Finset.range L, w ^ r = 0 by rw [this, mul_zero]
      have hwL : w ^ L = 1 := by
        rw [← exp_nat_mul]
        have hexp : (L : ℂ) * (2 * Real.pi * I * ((n : ℤ) - k) / L) =
            (((n : ℤ) - k) : ℂ) * (2 * Real.pi * I) := by
          field_simp
        rw [hexp]
        have hint := exp_int_mul_two_pi_mul_I ((n : ℤ) - k)
        push_cast at hint
        exact hint
      have hw1 : w ≠ 1 := by
        intro h1
        rw [exp_eq_one_iff] at h1
        obtain ⟨m, hm⟩ := h1
        have hpi : (2 : ℂ) * Real.pi * I ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            I_ne_zero
        have heq : (((n : ℤ) - k) : ℂ) = (m : ℂ) * L := by
          apply mul_right_cancel₀ hpi
          have hm' : 2 * Real.pi * I * ((n : ℤ) - k) = (m : ℂ) * (2 * Real.pi * I) * L := by
            exact (div_eq_iff hL0).mp hm
          linear_combination hm'
        have hz : (n : ℤ) - k = m * L := by exact_mod_cast heq
        have hn' : n < k + L := Finset.mem_range.mp hn
        have hm0 : m ≠ 0 := by
          rintro rfl
          omega
        rcases lt_or_gt_of_ne hm0 with hm_neg | hm_pos
        · have hm1 : m ≤ -1 := by omega
          have : m * (L : ℤ) ≤ -1 * (L : ℤ) :=
            Int.mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg L)
          omega
        · have hm1 : 1 ≤ m := by omega
          have : 1 * (L : ℤ) ≤ m * (L : ℤ) :=
            Int.mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg L)
          omega
      have hgeom := geom_sum_mul w L
      rw [hwL, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw1)
  rw [Finset.sum_congr rfl hinner]
  have hk_mem : k ∈ Finset.range (k + L) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_ite_eq' (Finset.range (k + L)) k (fun _ => (L : ℂ) * Q.coeff k)]
  simp [hk_mem, hL0]

/-- Truncated exponential series in `X` with parameter `u`: `∑_{q ≤ k} (u^q / q!) X^q`. -/
noncomputable def truncExpPoly (k : ℕ) (u : ℂ) : ℂ[X] :=
  ∑ q ∈ Finset.range (k + 1), C (u ^ q / (q.factorial : ℂ)) * X ^ q

lemma coeff_truncExpPoly (k : ℕ) (u : ℂ) (q : ℕ) :
    (truncExpPoly k u).coeff q = if q ≤ k then u ^ q / (q.factorial : ℂ) else 0 := by
  simp only [truncExpPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma natDegree_truncExpPoly_le (k : ℕ) (u : ℂ) : (truncExpPoly k u).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_truncExpPoly]
  simp [not_le.mpr hn]

lemma coeff_prod_truncExpPoly {α : Type*} (S : Finset α) (k : ℕ) (u : α → ℂ)
    {q : ℕ} (hq : q ≤ k) :
    (∏ j ∈ S, truncExpPoly k (u j)).coeff q =
      (∑ j ∈ S, u j) ^ q / (q.factorial : ℂ) := by
  classical
  induction S using Finset.induction_on generalizing q with
  | empty =>
    cases q with
    | zero => simp
    | succ q => simp [zero_pow (Nat.succ_ne_zero q), coeff_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun m p =>
        (truncExpPoly k (u a)).coeff m * (∏ j ∈ S, truncExpPoly k (u j)).coeff p]
    have hterm : ∀ m ∈ Finset.range (q + 1),
        (truncExpPoly k (u a)).coeff m * (∏ j ∈ S, truncExpPoly k (u j)).coeff (q - m) =
          (u a ^ m * (∑ j ∈ S, u j) ^ (q - m) * (q.choose m : ℂ)) / (q.factorial : ℂ) := by
      intro m hm
      have hmq : m ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hmk : m ≤ k := by omega
      have hqmk : q - m ≤ k := by omega
      rw [coeff_truncExpPoly, ih hqmk]
      simp only [hmk, ↓reduceIte]
      have hchoose : (q.factorial : ℂ) =
          (q.choose m : ℂ) * (m.factorial : ℂ) * ((q - m).factorial : ℂ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hmq).symm
      have hf1 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
      have hf2 : ((q - m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q - m).factorial_ne_zero
      have hfq : (q.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.factorial_ne_zero
      field_simp
      rw [hchoose]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← _root_.add_pow]

lemma natDegree_prod_truncExpPoly_le {α : Type*} (S : Finset α) (k : ℕ) (u : α → ℂ) :
    (∏ j ∈ S, truncExpPoly k (u j)).natDegree ≤ S.card * k := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_one_mul]
    exact (natDegree_mul_le).trans (by linarith [natDegree_truncExpPoly_le k (u a)])

/-- Reversed Hasse-derivative polynomial `∑_{q ≤ k} q! (hasseDeriv q P)(u) X^{k - q}`. -/
noncomputable def revHassePoly (P : ℂ[X]) (k : ℕ) (u : ℂ) : ℂ[X] :=
  ∑ q ∈ Finset.range (k + 1),
    C ((q.factorial : ℂ) * (hasseDeriv q P).eval u) * X ^ (k - q)

lemma coeff_revHassePoly (P : ℂ[X]) (k : ℕ) (u : ℂ) {n : ℕ} (hn : n ≤ k) :
    (revHassePoly P k u).coeff n =
      ((k - n).factorial : ℂ) * (hasseDeriv (k - n) P).eval u := by
  simp only [revHassePoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single (k - n)]
  · have hkn : k - (k - n) = n := by omega
    simp [hkn]
  · intro q hq hne
    have hq' : q ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have : n ≠ k - q := by omega
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma natDegree_revHassePoly_le (P : ℂ[X]) (k : ℕ) (u : ℂ) :
    (revHassePoly P k u).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  simp only [revHassePoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  refine Finset.sum_eq_zero fun q hq => ?_
  have : n ≠ k - q := by omega
  simp [this]

/-- In `d ≥ 2` coordinates, a single exponential polynomial `expPoly P μ (∑ j, s j)` is a sum of
`(d - 1) * P.natDegree + 1` coordinatewise products. -/
lemma isSumOfProducts_expPoly {d : ℕ} (hd : 2 ≤ d) (P : ℂ[X]) (μ : ℂ) :
    IsSumOfProducts (fun s : Fin d → ℝ≥0 => expPoly P μ (∑ j, (s j : ℝ)))
      ((d - 1) * P.natDegree + 1) := by
  let k := P.natDegree
  let L := (d - 1) * k + 1
  have hd0 : 0 < d := by omega
  let j₀ : Fin d := ⟨0, hd0⟩
  let rest : Finset (Fin d) := Finset.univ.erase j₀
  have hcard : rest.card = d - 1 := by simp [rest]
  let ζ (r : Fin L) : ℂ := exp (2 * Real.pi * I * (r : ℕ) / L)
  let f (r : Fin L) (j : Fin d) (u : ℝ≥0) : ℂ :=
    if j = j₀ then
      (L : ℂ)⁻¹ * exp (-2 * Real.pi * I * k * (r : ℕ) / L) *
        (revHassePoly P k (u : ℂ)).eval (ζ r) * exp (μ * u)
    else
      (truncExpPoly k (u : ℂ)).eval (ζ r) * exp (μ * u)
  refine ⟨f, fun s => ?_⟩
  let Q : ℂ[X] := revHassePoly P k (s j₀ : ℂ) * ∏ j ∈ rest, truncExpPoly k (s j : ℂ)
  have hdegQ : Q.natDegree < k + L := by
    have hle : Q.natDegree ≤ k + (d - 1) * k := by
      refine natDegree_mul_le.trans ?_
      have h1 := natDegree_revHassePoly_le P k (s j₀ : ℂ)
      have h2 := natDegree_prod_truncExpPoly_le rest k (fun j => (s j : ℂ))
      rw [hcard] at h2
      linarith
    have : k + (d - 1) * k < k + L := by dsimp [L]; omega
    exact lt_of_le_of_lt hle this
  have hkL : k < L := by
    have : 1 * k ≤ (d - 1) * k := Nat.mul_le_mul_right k (by omega)
    dsimp [L]
    omega
  have hcoeffQ : Q.coeff k = P.eval (∑ j : Fin d, (s j : ℂ)) := by
    rw [show Q = _ from rfl, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun m p =>
        (revHassePoly P k (s j₀ : ℂ)).coeff m *
          (∏ j ∈ rest, truncExpPoly k (s j : ℂ)).coeff p]
    have hsum_s : (s j₀ : ℂ) + ∑ j ∈ rest, (s j : ℂ) = ∑ j : Fin d, (s j : ℂ) :=
      Finset.add_sum_erase Finset.univ (fun j => (s j : ℂ)) (Finset.mem_univ j₀)
    let T := ∑ j ∈ rest, (s j : ℂ)
    have hanti : ∑ m ∈ Finset.range (k + 1),
        (revHassePoly P k (s j₀ : ℂ)).coeff m *
          (∏ j ∈ rest, truncExpPoly k (s j : ℂ)).coeff (k - m) =
        ∑ q ∈ Finset.range (k + 1), (hasseDeriv q P).eval (s j₀ : ℂ) * T ^ q := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqk : q ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      have hsub : k - (k - q) = q := by omega
      simp only [Nat.add_sub_cancel]
      rw [hsub, coeff_revHassePoly P k (s j₀ : ℂ) (Nat.sub_le k q), hsub,
        coeff_prod_truncExpPoly rest k (fun j => (s j : ℂ)) hqk]
      have hfq : (q.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.factorial_ne_zero
      dsimp [T]
      field_simp
    rw [hanti, ← hsum_s, add_comm (s j₀ : ℂ) T, ← taylor_eval,
      eval_eq_sum_range' (by rw [natDegree_taylor]; exact Nat.lt_succ_self k)]
    exact Finset.sum_congr rfl fun q _ => by rw [taylor_coeff]
  have hroots := coeff_eq_sum_rootsOfUnity Q hkL hdegQ
  rw [hcoeffQ, ← Fin.sum_univ_eq_sum_range] at hroots
  simp only [expPoly, Complex.ofReal_sum, hroots, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hprod_exp : exp (∑ j : Fin d, μ * (s j : ℂ)) = ∏ j : Fin d, exp (μ * (s j : ℂ)) :=
    Complex.exp_sum _ _
  have hsplit := (Finset.mul_prod_erase Finset.univ (fun j => f r j (s j))
    (Finset.mem_univ j₀)).symm
  have hsplit_exp := (Finset.mul_prod_erase Finset.univ (fun j => exp (μ * (s j : ℂ)))
    (Finset.mem_univ j₀)).symm
  rw [hsplit, hprod_exp, hsplit_exp]
  have hf0 : f r j₀ (s j₀) =
      (L : ℂ)⁻¹ * exp (-2 * Real.pi * I * k * (r : ℕ) / L) *
        (revHassePoly P k (s j₀ : ℂ)).eval (ζ r) * exp (μ * (s j₀ : ℂ)) := by
    simp [f]
  have hfrest : ∏ j ∈ rest, f r j (s j) =
      (∏ j ∈ rest, (truncExpPoly k (s j : ℂ)).eval (ζ r)) *
        ∏ j ∈ rest, exp (μ * (s j : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j hj => by
      simp [f, Finset.ne_of_mem_erase hj]
  have hevalQ : Q.eval (ζ r) =
      (revHassePoly P k (s j₀ : ℂ)).eval (ζ r) *
        ∏ j ∈ rest, (truncExpPoly k (s j : ℂ)).eval (ζ r) := by
    simp [Q, eval_mul, eval_prod]
  rw [hf0, hfrest, hevalQ]
  ring

/-! ### Function-to-tensor bridge and Alder–Strassen peeling lower bound -/

/-- If `v : α → V` spans `V`, any `R`-term coordinatewise product decomposition of
`s ↦ T (fun j => v (s j))` induces an `R`-term linear-functional decomposition of `T`. -/
lemma exists_linear_factors_of_span_eq_top {𝕜 α V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] {d R : ℕ} {v : α → V} (hv : Submodule.span 𝕜 (Set.range v) = ⊤)
    (T : MultilinearMap 𝕜 (fun _ : Fin d => V) 𝕜)
    (hK : IsSumOfProducts (fun s : Fin d → α => T fun j => v (s j)) R) :
    ∃ ℓ : Fin R → Fin d → (V →ₗ[𝕜] 𝕜),
      ∀ u : Fin d → V, T u = ∑ n, ∏ j, ℓ n j (u j) := by
  obtain ⟨f, hf⟩ := hK
  obtain ⟨κ, a, _, hsp, hli⟩ := exists_linearIndependent' 𝕜 v
  let B : Module.Basis κ 𝕜 V := Module.Basis.mk hli (hv ▸ hsp).ge
  let ℓ (n : Fin R) (j : Fin d) : V →ₗ[𝕜] 𝕜 := B.constr ℕ fun k => f n j (a k)
  refine ⟨ℓ, fun u => ?_⟩
  let T' : MultilinearMap 𝕜 (fun _ : Fin d => V) 𝕜 :=
    ∑ n : Fin R, (MultilinearMap.mkPiAlgebra 𝕜 (Fin d) 𝕜).compLinearMap (ℓ n)
  have heq : T = T' := Module.Basis.ext_multilinear (fun _ => B) fun k => by
    have hBk (j : Fin d) : B (k j) = v (a (k j)) := Module.Basis.mk_apply hli (hv ▸ hsp).ge (k j)
    have hℓB (n : Fin R) (j : Fin d) : ℓ n j (B (k j)) = f n j (a (k j)) :=
      B.constr_basis ℕ _ (k j)
    simp only [T', FunLike.coe_sum, Finset.sum_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, hℓB]
    simp_rw [hBk]
    exact hf fun j => a (k j)
  simpa [T'] using congrArg (· u) heq

/-- If every linear functional vanishing on `Set.range v` is zero, then `Set.range v` spans `V`. -/
lemma span_range_eq_top_of_dual {𝕜 α V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {v : α → V} (h : ∀ L : V →ₗ[𝕜] 𝕜, (∀ s, L (v s) = 0) → L = 0) :
    Submodule.span 𝕜 (Set.range v) = ⊤ := by
  by_contra hlt
  obtain ⟨L, hLne, hLmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hlt) inferInstance
  refine hLne (h L fun s => ?_)
  have hmem : L (v s) ∈ Submodule.map L (Submodule.span 𝕜 (Set.range v)) :=
    ⟨v s, Submodule.subset_span ⟨s, rfl⟩, rfl⟩
  rwa [hLmap, Submodule.mem_bot] at hmem

/-- Space of exponential-monomial coefficients `∀ i : ι, Fin (m₀ i) → ℂ`. -/
abbrev CoeffSpace {ι : Type*} (m₀ : ι → ℕ) : Type _ :=
  ∀ i : ι, Fin (m₀ i) → ℂ

/-- Single basis coordinate in `CoeffSpace m₀`. -/
noncomputable def singleCoeff {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) : CoeffSpace m₀ :=
  fun i q => if h : i = i₀ then if (h ▸ q) = q₀ then z else 0 else 0

@[simp] lemma singleCoeff_same {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) :
    singleCoeff i₀ q₀ z i₀ q₀ = z := by
  simp [singleCoeff]

lemma singleCoeff_of_ne_idx {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) {i : ι} (hi : i ≠ i₀) (q : Fin (m₀ i)) :
    singleCoeff i₀ q₀ z i q = 0 := by
  simp [singleCoeff, hi]

lemma singleCoeff_of_ne_deg {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ q : Fin (m₀ i₀)) (z : ℂ) (hq : q ≠ q₀) :
    singleCoeff i₀ q₀ z i₀ q = 0 := by
  simp [singleCoeff, hq]

lemma sum_comp_update {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (g : ℕ → M) (c : ι → ℕ) (i₀ : ι) (v : ℕ) :
    (∑ i, g (Function.update c i₀ v i)) + g (c i₀) = (∑ i, g (c i)) + g v := by
  rw [← Finset.add_sum_erase Finset.univ (fun i => g (Function.update c i₀ v i))
      (Finset.mem_univ i₀),
    ← Finset.add_sum_erase Finset.univ (fun i => g (c i)) (Finset.mem_univ i₀)]
  have her : ∑ i ∈ Finset.univ.erase i₀, g (Function.update c i₀ v i) =
      ∑ i ∈ Finset.univ.erase i₀, g (c i) :=
    Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]
  rw [her, Function.update_self]
  abel

lemma sum_update_nat {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (i₀ : ι) (v : ℕ) :
    (∑ i, Function.update c i₀ v i) + c i₀ = (∑ i, c i) + v :=
  sum_comp_update (fun n => n) c i₀ v

/-- The `d`-multilinear exponential-polynomial form with active cutoffs `c ≤ m₀`. -/
noncomputable def truncForm {ι : Type*} [Fintype ι] (d : ℕ) (m₀ c : ι → ℕ)
    (w : ι → ℕ → ℂ) (u : Fin d → ∀ i, Fin (m₀ i) → ℂ) : ℂ :=
  ∑ i : ι, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m₀ i) => ∑ j, (q j : ℕ) < c i),
    w i (∑ j, (q j : ℕ)) * ∏ j : Fin d, u j i (q j)

/-- Alder–Strassen peeling lower bound for `truncForm`. -/
lemma truncForm_rank_ge {ι : Type*} [Fintype ι] {d : ℕ} (hd : 2 ≤ d)
    (m₀ : ι → ℕ) :
    ∀ (S : ℕ) (c : ι → ℕ), ∑ i, c i = S → (∀ i, c i ≤ m₀ i) →
      ∀ (w : ι → ℕ → ℂ), (∀ i, 0 < c i → w i (c i - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → ((∀ i, Fin (m₀ i) → ℂ) →ₗ[ℂ] ℂ)),
      (∀ u, truncForm d m₀ c w u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ i, if c i = 0 then 0 else (d - 1) * (c i - 1) + 1) ≤ R := by
  let := Classical.decEq ι
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro c hS hcm w hw R ℓ hrepr
    by_cases hall : ∀ i, c i = 0
    · simp [hall]
    push Not at hall
    obtain ⟨i₀, hi₀_ne⟩ := hall
    have hi₀_pos : 0 < c i₀ := Nat.pos_of_ne_zero hi₀_ne
    have hm₀_pos : 0 < m₀ i₀ := lt_of_lt_of_le hi₀_pos (hcm i₀)
    have hd0 : 0 < d := by omega
    by_cases hc1 : c i₀ = 1
    · -- Case `c i₀ = 1`: kill `1` term in mode `0` and zero out coordinate `i₀` in modes `j ≥ 1`.
      let q₀ : Fin (m₀ i₀) := ⟨0, hm₀_pos⟩
      let e₀ : CoeffSpace m₀ := singleCoeff i₀ q₀ 1
      have hTe : truncForm d m₀ c w (fun _ => e₀) = w i₀ 0 := by
        simp only [truncForm]
        rw [Finset.sum_eq_single i₀]
        · rw [Finset.sum_eq_single (fun _ => q₀)]
          · simp [e₀, q₀]
          · intro q _ hne
            have : ∃ j, q j ≠ q₀ := by
              by_contra h; push Not at h; exact hne (funext h)
            obtain ⟨j, hj⟩ := this
            rw [Finset.prod_eq_zero (Finset.mem_univ j)]
            · simp
            · exact singleCoeff_of_ne_deg i₀ q₀ (q j) 1 hj
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [q₀, hc1]⟩) h
        · intro i _ hi
          refine Finset.sum_eq_zero fun q _ => ?_
          rw [Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd0⟩)]
          · simp
          · exact singleCoeff_of_ne_idx i₀ q₀ 1 hi (q ⟨0, hd0⟩)
        · simp
      have hw0 : w i₀ 0 ≠ 0 := by simpa [hc1] using hw i₀ hi₀_pos
      have hsum_ne : ∑ n : Fin R, ∏ j : Fin d, ℓ n j e₀ ≠ 0 := by
        rw [← hrepr]; exact hTe ▸ hw0
      obtain ⟨n₀, _, hn₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
      have hℓ0 : ℓ n₀ ⟨0, hd0⟩ e₀ ≠ 0 := fun h =>
        hn₀ (Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd0⟩) h)
      let kill : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        { toFun := fun x i => if i = i₀ then 0 else x i
          map_add' := fun a b => by
            ext i q; by_cases h : i = i₀ <;> simp [h]
          map_smul' := fun a b => by
            ext i q; by_cases h : i = i₀ <;> simp [h] }
      let φ₀ : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        kill - ((ℓ n₀ ⟨0, hd0⟩ e₀)⁻¹ • (ℓ n₀ ⟨0, hd0⟩).comp kill).smulRight e₀
      have hφ₀_kill (x : CoeffSpace m₀) : ℓ n₀ ⟨0, hd0⟩ (φ₀ x) = 0 := by
        simp only [φ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
        field_simp
        ring
      let c' : ι → ℕ := Function.update c i₀ 0
      have hS' : ∑ i, c' i < S := by
        have h := sum_update_nat c i₀ 0
        change (∑ i, c' i) + c i₀ = (∑ i, c i) + 0 at h
        omega
      have hc'm : ∀ i, c' i ≤ m₀ i := fun i => by
        by_cases h : i = i₀ <;> simp [c', h, hcm i]
      have hwc' : ∀ i, 0 < c' i → w i (c' i - 1) ≠ 0 := fun i hi => by
        have h : i ≠ i₀ := by rintro rfl; simp [c'] at hi
        simpa [c', h] using hw i (by simpa [c', h] using hi)
      let rem : Finset (Fin R) := Finset.univ.erase n₀
      have hRpos : 1 ≤ R := Fin.pos n₀
      let eRem : Fin (R - 1) ≃ rem :=
        (Fintype.equivFinOfCardEq (by simp [rem])).symm
      let φ (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        if j = ⟨0, hd0⟩ then φ₀ else kill
      let ℓ' (m : Fin (R - 1)) (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] ℂ :=
        (ℓ (eRem m).1 j).comp (φ j)
      have hrepr' (u : Fin d → CoeffSpace m₀) :
          truncForm d m₀ c' w u = ∑ m : Fin (R - 1), ∏ j, ℓ' m j (u j) := by
        have hT : truncForm d m₀ c' w u = truncForm d m₀ c w (fun j => φ j (u j)) := by
          simp only [truncForm]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i = i₀
          · rw [hi]
            have hL0 : (∑ q ∈ Finset.univ.filter
                (fun q : Fin d → Fin (m₀ i₀) => ∑ j, (q j : ℕ) < c' i₀),
                w i₀ (∑ j, (q j : ℕ)) * ∏ j, u j i₀ (q j)) = 0 :=
              Finset.sum_eq_zero fun q hq => by
                have := (Finset.mem_filter.mp hq).2
                simp [c'] at this
            rw [hL0]
            symm
            refine Finset.sum_eq_zero fun q _ => ?_
            let j₁ : Fin d := ⟨1, hd⟩
            have hj₁ : j₁ ≠ ⟨0, hd0⟩ := by simp [j₁, Fin.ext_iff]
            have hzero : φ j₁ (u j₁) i₀ (q j₁) = 0 := by simp [φ, hj₁, kill]
            rw [Finset.prod_eq_zero (Finset.mem_univ j₁) hzero, mul_zero]
          · simp only [c', Function.update_of_ne hi]
            refine Finset.sum_congr rfl fun q _ => ?_
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = ⟨0, hd0⟩
            · subst hj
              simp [φ, φ₀, kill, hi, e₀, singleCoeff_of_ne_idx i₀ q₀ 1 hi]
            · simp [φ, hj, kill, hi]
        rw [hT, hrepr]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ n₀)]
        have hdead : (∏ j : Fin d, ℓ n₀ j (φ j (u j))) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd0⟩) (by simp [φ, hφ₀_kill])
        rw [hdead, zero_add]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hih := ih (∑ i, c' i) hS' c' rfl hc'm w hwc' (R - 1) ℓ' hrepr'
      dsimp only [c'] at hih
      have hcost := sum_comp_update (fun n => if n = 0 then 0 else (d - 1) * (n - 1) + 1) c i₀ 0
      simp only [hc1, ↓reduceIte, Nat.sub_self, mul_zero, zero_add, add_zero, one_ne_zero] at hcost
      omega
    · -- Case `c i₀ ≥ 2`: peel `d - 1` terms in modes `0, …, d - 2` and shift mode `d - 1`.
      have hc2 : 2 ≤ c i₀ := by omega
      let q₀ : Fin (m₀ i₀) := ⟨0, hm₀_pos⟩
      let qTop : Fin (m₀ i₀) := ⟨c i₀ - 1, lt_of_lt_of_le (Nat.sub_lt hi₀_pos zero_lt_one) (hcm i₀)⟩
      let s₀ : CoeffSpace m₀ := singleCoeff i₀ q₀ 1
      let sTop : CoeffSpace m₀ := singleCoeff i₀ qTop 1
      have hqTop_ne : qTop ≠ q₀ := by
        intro h
        have := congrArg Fin.val h
        dsimp [qTop, q₀] at this
        omega
      -- Construct `r` killed indices for modes `0, …, r - 1` up to `r = d - 1`.
      have hpeel : ∀ r ≤ d - 1,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀)),
          D.card = r ∧
          (∀ j : Fin d, ¬ (j : ℕ) < r → ψ j = LinearMap.id) ∧
          (∀ j : Fin d, (j : ℕ) < r →
            ∃ c_j : CoeffSpace m₀ →ₗ[ℂ] ℂ, ∀ x, ψ j x = x - c_j x • sTop) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < r ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro r hr
        induction r with
        | zero =>
          exact ⟨∅, fun _ => LinearMap.id, by simp, fun _ _ => rfl,
            fun _ hj => absurd hj (Nat.not_lt_zero _), by simp⟩
        | succ r ihr =>
          obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := ihr (by omega)
          let jr : Fin d := ⟨r, by omega⟩
          let u (k : Fin d) : CoeffSpace m₀ := if k = jr then sTop else ψ k s₀
          have hTu : truncForm d m₀ c w u = w i₀ (c i₀ - 1) := by
            simp only [truncForm]
            rw [Finset.sum_eq_single i₀]
            · let qTarget : Fin d → Fin (m₀ i₀) := fun k => if k = jr then qTop else q₀
              have hqT_sum : ∑ k : Fin d, (qTarget k : ℕ) = c i₀ - 1 := by
                have hval (k : Fin d) : (qTarget k : ℕ) = if k = jr then c i₀ - 1 else 0 := by
                  by_cases hk : k = jr <;> simp [qTarget, hk, qTop, q₀]
                simp_rw [hval]
                simp
              rw [Finset.sum_eq_single qTarget]
              · rw [hqT_sum]
                suffices ∏ k : Fin d, u k i₀ (qTarget k) = 1 by rw [this, mul_one]
                refine Finset.prod_eq_one fun k _ => ?_
                by_cases hk : k = jr
                · subst hk; simp [u, qTarget, sTop]
                · obtain ⟨ck, hck⟩ | h_id :
                    (∃ ck : CoeffSpace m₀ →ₗ[ℂ] ℂ, ∀ x, ψ k x = x - ck x • sTop) ∨
                      ψ k = LinearMap.id := by
                    by_cases hkr : (k : ℕ) < r
                    · exact Or.inl (hψ_form k hkr)
                    · exact Or.inr (hψ_id k hkr)
                  · simp [u, hk, qTarget, hck, s₀, sTop,
                      singleCoeff_of_ne_deg i₀ qTop q₀ 1 hqTop_ne.symm]
                  · simp [u, hk, qTarget, h_id, s₀]
              · intro q hq hne
                have hqsum : ∑ k : Fin d, (q k : ℕ) < c i₀ := (Finset.mem_filter.mp hq).2
                by_cases hqjr : q jr = qTop
                · have hex : ∃ k ≠ jr, q k ≠ q₀ := by
                    by_contra h; push Not at h
                    refine hne (funext fun k => ?_)
                    by_cases hk : k = jr
                    · simp [qTarget, hk, hqjr]
                    · simp [qTarget, hk, h k hk]
                  obtain ⟨k, hk_ne, hqk_ne⟩ := hex
                  have hqk_zero : (q k : ℕ) = 0 := by
                    have hle : (q jr : ℕ) + (q k : ℕ) ≤ ∑ m : Fin d, (q m : ℕ) := by
                      rw [← Finset.add_sum_erase Finset.univ (fun m : Fin d => (q m : ℕ))
                        (Finset.mem_univ jr)]
                      exact Nat.add_le_add_left
                        (Finset.single_le_sum (f := fun m : Fin d => (q m : ℕ))
                          (fun _ _ => Nat.zero_le _)
                          (Finset.mem_erase.mpr ⟨hk_ne, Finset.mem_univ k⟩)) _
                    rw [hqjr] at hle
                    dsimp [qTop] at hle
                    omega
                  exact absurd (Fin.ext hqk_zero) hqk_ne
                · have hu0 : u jr i₀ (q jr) = 0 := by
                    simp [u, sTop, singleCoeff_of_ne_deg i₀ qTop (q jr) 1 hqjr]
                  rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
              · intro h
                exact absurd (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, by rw [hqT_sum]; omega⟩) h
            · intro i _ hi
              refine Finset.sum_eq_zero fun q _ => ?_
              have hu0 : u jr i (q jr) = 0 := by
                simp [u, sTop, singleCoeff_of_ne_idx i₀ qTop 1 hi]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
            · simp
          have hsum_sdiff : ∑ n ∈ Finset.univ \ D, ∏ k : Fin d, ℓ n k (u k) =
              w i₀ (c i₀ - 1) := by
            rw [← hTu, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
            have hD0 : ∑ n ∈ D, ∏ k : Fin d, ℓ n k (u k) = 0 :=
              Finset.sum_eq_zero fun n hn => by
                obtain ⟨j, hjr, hkill⟩ := hDkill n hn
                have hj_ne : j ≠ jr := by simp [jr, Fin.ext_iff]; omega
                exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [u, hj_ne, hkill])
            rw [hD0, add_zero]
          obtain ⟨nr, hnr_mem, hnr_prod⟩ :=
            Finset.exists_ne_zero_of_sum_ne_zero (hsum_sdiff.symm ▸ hw i₀ hi₀_pos)
          have hnr_notD : nr ∉ D := (Finset.mem_sdiff.mp hnr_mem).2
          have hℓ_top : ℓ nr jr sTop ≠ 0 := fun h =>
            hnr_prod (Finset.prod_eq_zero (Finset.mem_univ jr) (by simp [u, h]))
          let cr : CoeffSpace m₀ →ₗ[ℂ] ℂ := (ℓ nr jr sTop)⁻¹ • ℓ nr jr
          let ψr : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ := LinearMap.id - cr.smulRight sTop
          have hψr_kill (x : CoeffSpace m₀) : ℓ nr jr (ψr x) = 0 := by
            simp only [ψr, cr, LinearMap.sub_apply, LinearMap.id_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp
            ring
          let ψ' (k : Fin d) : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ := if k = jr then ψr else ψ k
          refine ⟨insert nr D, ψ', ?_, ?_, ?_, ?_⟩
          · rw [Finset.card_insert_of_notMem hnr_notD, hDcard]
          · intro k hk
            have hk_ne : k ≠ jr := by simp [jr, Fin.ext_iff]; omega
            simp only [ψ', hk_ne, ↓reduceIte]
            exact hψ_id k (by omega)
          · intro k hk
            by_cases hkj : k = jr
            · subst hkj; exact ⟨cr, fun x => by simp [ψ', ψr]⟩
            · simp only [ψ', hkj, ↓reduceIte]
              exact hψ_form k (by simp [jr, Fin.ext_iff] at hkj; omega)
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hnD
            · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψr_kill]⟩
            · obtain ⟨j, hjr, hkill⟩ := hDkill n hnD
              have hj_ne : j ≠ jr := by simp [jr, Fin.ext_iff]; omega
              exact ⟨j, by omega, fun x => by simp [ψ', hj_ne, hkill]⟩
      obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := hpeel (d - 1) le_rfl
      let jLast : Fin d := ⟨d - 1, by omega⟩
      let truncLow : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        { toFun := fun x i q => if i = i₀ then if (q : ℕ) + 1 < c i₀ then x i q else 0 else x i q
          map_add' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : (q : ℕ) + 1 < c i₀ <;> simp [hi, hq]
            · simp [hi]
          map_smul' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : (q : ℕ) + 1 < c i₀ <;> simp [hi, hq]
            · simp [hi] }
      let shiftUp : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        { toFun := fun x i q =>
            if i = i₀ then
              if hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c i₀ then
                x i₀ ⟨(q : ℕ) - 1, by have := hcm i₀; omega⟩
              else 0
            else x i q
          map_add' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c i₀ <;> simp [hi, hq]
            · simp [hi]
          map_smul' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c i₀ <;> simp [hi, hq]
            · simp [hi] }
      let φ (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        if j = jLast then shiftUp else (ψ j).comp truncLow
      let c' : ι → ℕ := Function.update c i₀ (c i₀ - 1)
      let w' : ι → ℕ → ℂ := Function.update w i₀ (fun k => w i₀ (k + 1))
      have hS' : ∑ i, c' i < S := by
        have h := sum_update_nat c i₀ (c i₀ - 1)
        change (∑ i, c' i) + c i₀ = (∑ i, c i) + (c i₀ - 1) at h
        omega
      have hc'm : ∀ i, c' i ≤ m₀ i := fun i => by
        by_cases h : i = i₀
        · rw [h]; simp only [c', Function.update_self]; have := hcm i₀; omega
        · simp [c', h, hcm i]
      have hwc' : ∀ i, 0 < c' i → w' i (c' i - 1) ≠ 0 := fun i hi => by
        by_cases h : i = i₀
        · rw [h]
          simp only [c', w', Function.update_self]
          have hsub : c i₀ - 1 - 1 + 1 = c i₀ - 1 := by omega
          rw [hsub]
          exact hw i₀ hi₀_pos
        · simp only [c', w', Function.update_of_ne h] at hi ⊢
          exact hw i hi
      have hdR : d - 1 ≤ R := by
        have := Finset.card_le_univ D
        simpa [hDcard] using this
      let rem : Finset (Fin R) := Finset.univ \ D
      have hrem_card : Fintype.card rem = R - (d - 1) := by
        rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ D),
          Finset.card_univ, Fintype.card_fin, hDcard]
      let eRem : Fin (R - (d - 1)) ≃ rem := (Fintype.equivFinOfCardEq hrem_card).symm
      let ℓ' (m : Fin (R - (d - 1))) (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] ℂ :=
        (ℓ (eRem m).1 j).comp (φ j)
      have hrepr' (u : Fin d → CoeffSpace m₀) :
          truncForm d m₀ c' w' u = ∑ m : Fin (R - (d - 1)), ∏ j, ℓ' m j (u j) := by
        have hT : truncForm d m₀ c' w' u = truncForm d m₀ c w (fun j => φ j (u j)) := by
          simp only [truncForm]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i = i₀
          · rw [hi]
            simp only [c', w', Function.update_self]
            let S_hi := Finset.univ.filter
              (fun q : Fin d → Fin (m₀ i₀) => ∑ j, (q j : ℕ) < c i₀)
            let S_hi1 := S_hi.filter (fun q => 1 ≤ (q jLast : ℕ))
            have hdrop0 : ∑ q ∈ S_hi,
                w i₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) i₀ (q j) =
              ∑ q ∈ S_hi1,
                w i₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) i₀ (q j) := by
              rw [← Finset.sum_filter_add_sum_filter_not S_hi (fun q => 1 ≤ (q jLast : ℕ))]
              suffices ∑ q ∈ S_hi.filter (fun q => ¬ 1 ≤ (q jLast : ℕ)),
                  w i₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) i₀ (q j) = 0 by
                rw [this, add_zero]
              refine Finset.sum_eq_zero fun q hq => ?_
              have hq0 : ¬ (1 ≤ (q jLast : ℕ) ∧ (q jLast : ℕ) < c i₀) :=
                fun h => (Finset.mem_filter.mp hq).2 h.1
              have hz : φ jLast (u jLast) i₀ (q jLast) = 0 := by
                simp [φ, shiftUp, hq0]
              rw [Finset.prod_eq_zero (Finset.mem_univ jLast) hz, mul_zero]
            rw [hdrop0]
            let toHi (q' : Fin d → Fin (m₀ i₀)) (j : Fin d) : Fin (m₀ i₀) :=
              if h : j = jLast ∧ (q' jLast : ℕ) + 1 < m₀ i₀ then
                ⟨(q' jLast : ℕ) + 1, h.2⟩
              else q' j
            let toLow (q : Fin d → Fin (m₀ i₀)) (j : Fin d) : Fin (m₀ i₀) :=
              if j = jLast then ⟨(q jLast : ℕ) - 1, by have := (q jLast).2; omega⟩ else q j
            have htoHi (q' : Fin d → Fin (m₀ i₀))
                (hsum' : ∑ j, (q' j : ℕ) < c i₀ - 1) :
                (q' jLast : ℕ) + 1 < m₀ i₀ ∧
                  ∑ j, (toHi q' j : ℕ) = (∑ j, (q' j : ℕ)) + 1 := by
              have hlast_lt : (q' jLast : ℕ) + 1 < m₀ i₀ := by
                have hle := Finset.single_le_sum (f := fun j : Fin d => (q' j : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                have := hcm i₀
                omega
              refine ⟨hlast_lt, ?_⟩
              have h := sum_update_nat (fun j => (q' j : ℕ)) jLast ((q' jLast : ℕ) + 1)
              have heq : ∑ j, (toHi q' j : ℕ) =
                  ∑ j, Function.update (fun k => (q' k : ℕ)) jLast ((q' jLast : ℕ) + 1) j :=
                Finset.sum_congr rfl fun j _ => by
                  by_cases hj : j = jLast <;> simp [toHi, hj, hlast_lt]
              rw [heq]
              omega
            refine Finset.sum_nbij' toHi toLow ?_ ?_ ?_ ?_ ?_
            · intro q' hq'
              obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' (Finset.mem_filter.mp hq').2
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
              · rw [hsum_hi]; have := (Finset.mem_filter.mp hq').2; omega
              · simp [toHi, hlast_lt]
            · intro q hq
              have hq_sum : ∑ j, (q j : ℕ) < c i₀ :=
                (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
              have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have h := sum_update_nat (fun j => (q j : ℕ)) jLast ((q jLast : ℕ) - 1)
              have heq : ∑ j, (toLow q j : ℕ) =
                  ∑ j, Function.update (fun k => (q k : ℕ)) jLast ((q jLast : ℕ) - 1) j :=
                Finset.sum_congr rfl fun j _ => by
                  by_cases hj : j = jLast <;> simp [toLow, hj]
              rw [← heq] at h
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            · intro q' hq'
              obtain ⟨hlast_lt, _⟩ := htoHi q' (Finset.mem_filter.mp hq').2
              ext j
              by_cases hj : j = jLast <;> simp [toLow, toHi, hj, hlast_lt]
            · intro q hq
              have hq_sum : ∑ j, (q j : ℕ) < c i₀ :=
                (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
              have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have hlast_lt : (q jLast : ℕ) - 1 + 1 < m₀ i₀ := by
                have hle := Finset.single_le_sum (f := fun j : Fin d => (q j : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                have := hcm i₀
                omega
              ext j
              by_cases hj : j = jLast
              · subst hj; simp [toHi, toLow, hlast_lt]; omega
              · simp [toHi, toLow, hj]
            · intro q' hq'
              have hsum' : ∑ j, (q' j : ℕ) < c i₀ - 1 := (Finset.mem_filter.mp hq').2
              obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' hsum'
              rw [hsum_hi]
              congr 1
              refine Finset.prod_congr rfl fun j _ => ?_
              have hqj_lt : (q' j : ℕ) + 1 < c i₀ := by
                have hle := Finset.single_le_sum (f := fun k : Fin d => (q' k : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                omega
              by_cases hj : j = jLast
              · subst hj
                have hcond : 1 ≤ (q' jLast : ℕ) + 1 ∧ (q' jLast : ℕ) + 1 < c i₀ := by omega
                simp [φ, shiftUp, toHi, hlast_lt, hcond]
              · have hj_lt : (j : ℕ) < d - 1 := by
                  simp [jLast, Fin.ext_iff] at hj; omega
                obtain ⟨cj, hcj⟩ := hψ_form j hj_lt
                have hq_ne_top : q' j ≠ qTop := by
                  intro h; have := congrArg Fin.val h; dsimp [qTop] at this; omega
                simp [φ, hj, toHi, hcj, truncLow, hqj_lt, sTop,
                  singleCoeff_of_ne_deg i₀ qTop (q' j) 1 hq_ne_top]
          · simp only [c', w', Function.update_of_ne hi]
            refine Finset.sum_congr rfl fun q _ => ?_
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = jLast
            · subst hj; simp [φ, shiftUp, hi]
            · have hj_lt : (j : ℕ) < d - 1 := by
                simp [jLast, Fin.ext_iff] at hj; omega
              obtain ⟨cj, hcj⟩ := hψ_form j hj_lt
              simp [φ, hj, hcj, truncLow, hi, sTop,
                singleCoeff_of_ne_idx i₀ qTop 1 hi]
        rw [hT, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
        have hdead : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            obtain ⟨j, hj_lt, hkill⟩ := hDkill n hn
            have hj_ne : j ≠ jLast := by simp [jLast, Fin.ext_iff]; omega
            exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [φ, hj_ne, hkill])
        rw [hdead, add_zero]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hih := ih (∑ i, c' i) hS' c' rfl hc'm w' hwc' (R - (d - 1)) ℓ' hrepr'
      dsimp only [c'] at hih
      have hcost :=
        sum_comp_update (fun n => if n = 0 then 0 else (d - 1) * (n - 1) + 1) c i₀ (c i₀ - 1)
      have hc'_ne : c i₀ - 1 ≠ 0 := by omega
      have hmul : (d - 1) * (c i₀ - 1) = (d - 1) * (c i₀ - 1 - 1) + (d - 1) := by
        have : c i₀ - 1 = (c i₀ - 1 - 1) + 1 := by omega
        nth_rw 1 [this]
        rw [mul_add, mul_one]
      simp only [hi₀_ne, hc'_ne, ↓reduceIte, hmul] at hcost
      omega

/-- Multinomial expansion of `expPoly P μ (∑ j, s j)` into `truncForm` terms. -/
lemma sum_expPoly_eq_truncForm {ι : Type*} [Fintype ι] (d : ℕ) (rate : ι → ℂ)
    (P : ι → ℂ[X]) (s : Fin d → ℝ≥0) :
    (∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
      truncForm d (fun i => (P i).natDegree + 1) (fun i => (P i).natDegree + 1)
        (fun i k => (k.factorial : ℂ) * (P i).coeff k)
        (fun j i q => ((s j : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
          exp (rate i * (s j : ℂ))) := by
  simp only [truncForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  let m := (P i).natDegree + 1
  have hprod_eq : ∀ q : Fin d → Fin m,
      (∏ j : Fin d, ((s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
        exp (rate i * (s j : ℂ))) =
      (∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
        exp (rate i * ∑ j : Fin d, (s j : ℂ)) := fun q => by
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum]
  simp_rw [hprod_eq, ← mul_assoc, ← Finset.sum_mul]
  simp only [expPoly, Complex.ofReal_sum]
  congr 1
  -- Evaluate `P i` via `∏ j, truncExpPoly (P i).natDegree (s j)`!
  let k := (P i).natDegree
  have hP : (P i).eval (∑ j : Fin d, (s j : ℂ)) =
      ∑ n ∈ Finset.range m, (P i).coeff n * (∑ j : Fin d, (s j : ℂ)) ^ n :=
    eval_eq_sum_range _
  rw [hP]
  -- Partition `{q : Fin d → Fin m | ∑ j, q j < m}` by `n = ∑ j, q j < m`
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun q : Fin d → Fin m => ∑ j, (q j : ℕ))
    (t := Finset.range m)
    (fun _ hq => Finset.mem_range.mpr (Finset.mem_filter.mp hq).2)]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hcongr_n :
      ∑ q ∈ (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
          (fun q => (∑ j, (q j : ℕ)) = n),
        (((∑ j, (q j : ℕ)).factorial : ℂ) * (P i).coeff (∑ j, (q j : ℕ))) *
          ∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ) =
      ∑ q ∈ (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
          (fun q => (∑ j, (q j : ℕ)) = n),
        ((n.factorial : ℂ) * (P i).coeff n) *
          ∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ) :=
    Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2]
  rw [← hcongr_n |> Eq.symm]
  have hmultinom :
      ∑ q ∈ (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
          (fun q => (∑ j, (q j : ℕ)) = n),
        ((n.factorial : ℂ) * (P i).coeff n) *
          ∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ) =
      (P i).coeff n * (∑ j : Fin d, (s j : ℂ)) ^ n := by
    have hcoeff := coeff_prod_truncExpPoly (Finset.univ : Finset (Fin d)) k
      (fun j => (s j : ℂ)) hnk
    have hexpand : (∏ j : Fin d, truncExpPoly k (s j : ℂ)) =
        ∑ q : Fin d → Fin m,
          C (∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
            X ^ (∑ j : Fin d, (q j : ℕ)) := by
      have htrunc (j : Fin d) : truncExpPoly k (s j : ℂ) =
          ∑ q : Fin m, C ((s j : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ) := by
        simpa [truncExpPoly, m, k] using (Fin.sum_univ_eq_sum_range
          (fun q : ℕ => C ((s j : ℂ) ^ q / (q.factorial : ℂ)) * X ^ q) m).symm
      simp_rw [htrunc]
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_prod C]
    rw [hexpand, finsetSum_coeff] at hcoeff
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      ← Finset.sum_filter] at hcoeff
    have hfilt : (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
        (fun q => (∑ j, (q j : ℕ)) = n) =
        Finset.univ.filter (fun q : Fin d → Fin m => n = ∑ j, (q j : ℕ)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hnm : n < m := Finset.mem_range.mp hn
      omega
    rw [hfilt, ← Finset.mul_sum, hcoeff]
    have hfn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  exact hmultinom.symm

/-- Coordinate projection `(x : CoeffSpace m₀) ↦ x i q` as a linear map. -/
def projCoeff {ι : Type*} {m₀ : ι → ℕ} (i : ι) (q : Fin (m₀ i)) : CoeffSpace m₀ →ₗ[ℂ] ℂ where
  toFun x := x i q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Bundled `truncForm` as a `MultilinearMap`. -/
noncomputable def truncMultilinearMap {ι : Type*} [Fintype ι] (d : ℕ) (m₀ c : ι → ℕ)
    (w : ι → ℕ → ℂ) : MultilinearMap ℂ (fun _ : Fin d => CoeffSpace m₀) ℂ :=
  ∑ i : ι, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m₀ i) => ∑ j, (q j : ℕ) < c i),
    w i (∑ j, (q j : ℕ)) •
      (MultilinearMap.mkPiAlgebra ℂ (Fin d) ℂ).compLinearMap (fun j => projCoeff i (q j))

lemma truncMultilinearMap_apply {ι : Type*} [Fintype ι] (d : ℕ) (m₀ c : ι → ℕ)
    (w : ι → ℕ → ℂ) (u : Fin d → CoeffSpace m₀) :
    truncMultilinearMap d m₀ c w u = truncForm d m₀ c w u := by
  simp [truncMultilinearMap, truncForm, projCoeff]

/-- Exponential-monomial evaluation vectors `(s^q / q!) exp (rate i * s)` span
`∀ i, Fin (m₀ i) → ℂ` when `rate` is injective. -/
lemma span_expMonomial_eq_top {ι : Type*} [Finite ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (m₀ : ι → ℕ) :
    Submodule.span ℂ
      (Set.range fun s : ℝ≥0 => fun (i : ι) (q : Fin (m₀ i)) =>
        ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate i * (s : ℂ))) = ⊤ := by
  cases nonempty_fintype ι
  classical
  refine span_range_eq_top_of_dual fun L hL => ?_
  let a (i : ι) (q : Fin (m₀ i)) : ℂ := L (singleCoeff i q 1)
  have hL_expand (x : ∀ i, Fin (m₀ i) → ℂ) :
      L x = ∑ i : ι, ∑ q : Fin (m₀ i), a i q * x i q := by
    have hx : x = ∑ i : ι, ∑ q : Fin (m₀ i), x i q • singleCoeff i q 1 := by
      ext i₀ q₀
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single q₀]
        · simp
        · intro q _ hq
          simp [singleCoeff_of_ne_deg i₀ q q₀ 1 hq.symm]
        · simp
      · intro i _ hi
        exact Finset.sum_eq_zero fun q _ => by simp [singleCoeff_of_ne_idx i q 1 hi.symm]
      · simp
    conv_lhs => rw [hx]
    simp [map_sum, map_smul, a, mul_comm]
  let Q (i : ι) : ℂ[X] :=
    ∑ q : Fin (m₀ i), C (a i q / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  have hQ0 : ∀ i, Q i = 0 := by
    refine eq_zero_of_sum_expPoly_eq_zero' hinj Q fun u hu => ?_
    have hs := hL ⟨u, hu.le⟩
    rw [hL_expand] at hs
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Q, expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    change (a i q / ((q : ℕ).factorial : ℂ)) * (u : ℂ) ^ (q : ℕ) * exp (rate i * (u : ℂ)) =
      a i q * (((u : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate i * (u : ℂ)))
    ring
  have ha0 (i : ι) (q : Fin (m₀ i)) : a i q = 0 := by
    have hc := congrArg (fun p => p.coeff (q : ℕ)) (hQ0 i)
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
    rw [Finset.sum_eq_single q] at hc
    · simp only [↓reduceIte, mul_one] at hc
      have hfq : ((q : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℕ).factorial_ne_zero
      exact (div_eq_zero_iff.mp hc).resolve_right hfq
    · intro q' _ hne
      have : (q : ℕ) ≠ (q' : ℕ) := fun h => hne (Fin.ext h.symm)
      simp [this]
    · simp
  ext x
  simp [hL_expand, ha0]

/-- **Exact `d`-way complex Hankel rank of exponential polynomials (`d ≥ 2`).** -/
theorem separableRank_sum_expPoly {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    separableRank (fun s : Fin d → ℝ≥0 => ∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
      (∑ i, ((d - 1) * (P i).natDegree + 1) : ℕ) := by
  classical
  refine le_antisymm ?_ ?_
  · exact iInf₂_le _ (IsSumOfProducts.finsetSum fun i =>
      isSumOfProducts_expPoly hd (P i) (rate i))
  · refine le_iInf₂ fun R hR => ?_
    let m₀ (i : ι) : ℕ := (P i).natDegree + 1
    let w (i : ι) (k : ℕ) : ℂ := (k.factorial : ℂ) * (P i).coeff k
    let v (s : ℝ≥0) (i : ι) (q : Fin (m₀ i)) : ℂ :=
      ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate i * (s : ℂ))
    have hK_eq : (fun s : Fin d → ℝ≥0 => ∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
        fun s => truncMultilinearMap d m₀ m₀ w (fun j => v (s j)) := by
      funext s
      rw [truncMultilinearMap_apply, sum_expPoly_eq_truncForm]
    rw [hK_eq] at hR
    obtain ⟨ℓ, hℓ⟩ := exists_linear_factors_of_span_eq_top (span_expMonomial_eq_top hinj m₀)
      (truncMultilinearMap d m₀ m₀ w) hR
    simp_rw [truncMultilinearMap_apply] at hℓ
    have hw : ∀ i, 0 < m₀ i → w i (m₀ i - 1) ≠ 0 := fun i _ => by
      dsimp [w, m₀]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (P i).natDegree.factorial_ne_zero)
        (leadingCoeff_ne_zero.mpr (hP i))
    have hge := truncForm_rank_ge hd m₀ (∑ i, m₀ i) m₀ rfl (fun _ => le_rfl) w hw R ℓ hℓ
    have hsum : (∑ i, if m₀ i = 0 then 0 else (d - 1) * (m₀ i - 1) + 1) =
        ∑ i, ((d - 1) * (P i).natDegree + 1) :=
      Finset.sum_congr rfl fun i _ => by simp [m₀]
    rw [hsum] at hge
    exact_mod_cast hge

/-- **Exact `d`-way complex radial rank of exponential polynomials (`d ≥ 2`).** -/
theorem separableRank_radial_sum_expPoly {d : ℕ} (hd : 2 ≤ d) {ι : Type*} [Fintype ι]
    {rate : ι → ℂ} (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    separableRank (fun x : Fin d → ℝ => ∑ i, expPoly (P i) (rate i) (∑ j, x j ^ 2)) =
      (∑ i, ((d - 1) * (P i).natDegree + 1) : ℕ) := by
  rw [separableRank_radial_eq_hankel d (fun t => ∑ i, expPoly (P i) (rate i) t),
    separableRank_sum_expPoly hd hinj P hP]

end KernelRank
