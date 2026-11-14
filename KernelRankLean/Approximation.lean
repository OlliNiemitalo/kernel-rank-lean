import KernelRankLean.Main

open Complex Polynomial
open scoped Topology

namespace KernelRank

/-!
# Universal approximation and exact border-rank bounds for radial kernels

This module complements `KernelRankLean.Main` with three approximation-theoretic results:

* **Two-variable slice lower semicontinuity and exact complex border rank
  (`separableRank_fin2_le_of_tendsto`, `separableRank_padTwo_le_of_tendsto`,
  `totalCost_le_of_tendsto_radial_profile`,
  `sum_natDegree_add_one_le_of_tendsto_radial_complex`,
  `exists_rank_le_sum_natDegree_add_one_tendstoUniformlyOn_radial_complex`):** over any Hausdorff
  topological field, two-variable separable rank is closed under pointwise limits. Padding two
  coordinates by zeros gives the universal lower bound `totalCost cs` (2-D rank) on real border
  rank in every dimension `d ≥ 2`, and determines the exact pointwise and compact-open complex
  border rank `∑ μ ∈ S, (deg P_μ + 1)` of every radial exponential polynomial.
* **Sharpness and strict non-sharpness of `borderTotalCost` in `d = 3`
  (`not_exists_rank_le_two_tendsto_radial_cos`,
  `not_exists_rank_le_four_tendsto_radial_sq_mul_cos`,
  `exists_rank_le_five_tendstoUniformlyOn_radial_sq_mul_cos`):** the polynomial adjugate trace
  invariant `0 ≤ trace ((adjugate S₀ * S₁) ^ 2)` proves that `cos(‖x‖²)` on `ℝ³` has exact
  pointwise and compact-open real border rank `3 = borderTotalCost 3`, whereas `‖x‖² cos(‖x‖²)` on
  `ℝ³` has exact pointwise and compact-open real border rank `5`—strictly separating complex border
  rank (`4`), real border rank (`5`), radial multi-Gaussian border rank / exact complex rank (`6`),
  and exact real rank (`7`).
* **Equal-width harmonic complex-Gaussian universal approximation
  (`exists_harmonic_gaussian_uniform_approx`):** every continuous radial profile `ψ` on `[0, ∞)`
  with `lim_{s → ∞} ψ(s) = 0` can be approximated uniformly across *all* of `ℝ^d` (`d ≥ 2`) by
  finite-rank multi-Gaussian kernels sharing any prescribed positive decay parameter `α > 0` and
  equally spaced harmonic frequencies `m ω₀`.
-/

section LowerSemicontinuity

private lemma det_mul_eq_zero_of_lt {𝕜 : Type*} [Field 𝕜] {r : ℕ}
    (U : Matrix (Fin (r + 1)) (Fin r) 𝕜) (V : Matrix (Fin r) (Fin (r + 1)) 𝕜) :
    (U * V).det = 0 := by
  by_contra hne
  have hunit : IsUnit (U * V) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
  obtain ⟨M, hM⟩ := hunit.exists_left_inv
  have hinj : Function.Injective (Matrix.mulVecLin V) := by
    intro v₁ v₂ hv
    have hv' : V.mulVec v₁ = V.mulVec v₂ := hv
    have h1 : (M * (U * V)).mulVec v₁ = (M * (U * V)).mulVec v₂ := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hv']
    simpa [hM] using h1
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun] at hle
  omega

private lemma isSumOfProducts_mono {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X : ι → Type*} [Nonempty ι] {K : (∀ i, X i) → 𝕜} {m n : ℕ} (hmn : m ≤ n)
    (hK : IsSumOfProducts K m) : IsSumOfProducts K n := by
  obtain ⟨f, hf⟩ := hK
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨fun k i x => if h : (k : ℕ) < m then f ⟨k, h⟩ i x else 0, fun x => ?_⟩
  have h1 : (∑ k : Fin n, ∏ i : ι,
      (if h : (k : ℕ) < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜))) =
      ∑ k ∈ Finset.range n, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) :=
    Fin.sum_univ_eq_sum_range
      (fun k => ∏ i : ι, if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜)) n
  have h2 : (∑ k ∈ Finset.range m, ∏ i : ι,
      (if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜))) =
      ∑ k ∈ Finset.range n, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) := by
    refine Finset.sum_subset (Finset.range_mono hmn) fun k _ hk => ?_
    have hnot : ¬ k < m := by simpa using hk
    simp only [hnot, ↓reduceDIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) rfl
  have h3 : (∑ k : Fin m, ∏ i : ι, f k i (x i)) =
      ∑ k ∈ Finset.range m, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ∏ i : ι, if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜)) m]
    refine Finset.sum_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => ?_
    simp [k.isLt]
  rw [hf, h3, h2, ← h1]

private lemma exists_submatrix_det_ne_zero_of_not_isSumOfProducts {𝕜 α : Type*} [Field 𝕜]
    {K : (Fin 2 → α) → 𝕜} {r : ℕ} (hnot : ¬ IsSumOfProducts K r) :
    ∀ k ≤ r + 1, ∃ (x y : Fin k → α),
      (Matrix.of fun p q => K (fin2Vec (x q) (y p))).det ≠ 0
  | 0, _ => ⟨Fin.elim0, Fin.elim0, by simp⟩
  | k + 1, hk => by
    obtain ⟨x, y, hdet⟩ :=
      exists_submatrix_det_ne_zero_of_not_isSumOfProducts hnot k (by omega)
    let A : Matrix (Fin k) (Fin k) 𝕜 := Matrix.of fun p q => K (fin2Vec (x q) (y p))
    have hA_det : A.det ≠ 0 := hdet
    let K_app (z : Fin 2 → α) : 𝕜 :=
      ∑ p : Fin k, K (fin2Vec (z 0) (y p)) *
        ∑ q : Fin k, A⁻¹ q p * K (fin2Vec (x q) (z 1))
    have hK_app_prod : IsSumOfProducts K_app k := by
      refine ⟨fun p => fin2Vec (fun u => K (fin2Vec u (y p)))
        (fun v => ∑ q : Fin k, A⁻¹ q p * K (fin2Vec (x q) v)), fun z => ?_⟩
      simp [K_app, Fin.prod_univ_two]
    have hK_app_r : IsSumOfProducts K_app r :=
      isSumOfProducts_mono (by omega) hK_app_prod
    have hne_fun : K ≠ K_app := fun heq => hnot (heq ▸ hK_app_r)
    obtain ⟨z₀, hz₀⟩ : ∃ z₀, K z₀ ≠ K_app z₀ := Function.ne_iff.mp hne_fun
    let x' : Fin k ⊕ Fin 1 → α := Sum.elim x (fun _ => z₀ 0)
    let y' : Fin k ⊕ Fin 1 → α := Sum.elim y (fun _ => z₀ 1)
    let B : Matrix (Fin k) (Fin 1) 𝕜 := Matrix.of fun p _ => K (fin2Vec (z₀ 0) (y p))
    let C : Matrix (Fin 1) (Fin k) 𝕜 := Matrix.of fun _ q => K (fin2Vec (x q) (z₀ 1))
    let D : Matrix (Fin 1) (Fin 1) 𝕜 := Matrix.of fun _ _ => K (fin2Vec (z₀ 0) (z₀ 1))
    let _ : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA_det)
    have hinv_eq : ⅟A = A⁻¹ := Matrix.invOf_eq_nonsing_inv A
    have hfb_det : (Matrix.fromBlocks A B C D).det ≠ 0 := by
      rw [Matrix.det_fromBlocks₁₁, hinv_eq]
      refine mul_ne_zero hA_det ?_
      rw [Matrix.det_fin_one]
      have hschur : (D - C * A⁻¹ * B) 0 0 = K z₀ - K_app z₀ := by
        have hz_eta : fin2Vec (z₀ 0) (z₀ 1) = z₀ := fin2Vec_eta z₀
        change D 0 0 - ((C * A⁻¹) * B) 0 0 = K z₀ - K_app z₀
        simp only [D, C, B, K_app, Matrix.of_apply, Matrix.mul_apply, hz_eta]
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring
      rw [hschur]
      exact sub_ne_zero.mpr hz₀
    let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
    refine ⟨x' ∘ e.symm, y' ∘ e.symm, ?_⟩
    have hsub : (Matrix.of fun p q : Fin (k + 1) =>
        K (fin2Vec ((x' ∘ e.symm) q) ((y' ∘ e.symm) p))) =
        Matrix.reindex e e (Matrix.fromBlocks A B C D) := by
      ext p q
      rcases h1 : e.symm p with p₀ | p₁ <;> rcases h2 : e.symm q with q₀ | q₁ <;>
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, h1, h2, x', y', A, B, C, D,
          Matrix.fromBlocks]
    rw [hsub, Matrix.det_reindex_self]
    exact hfb_det

/-- **Pointwise closure of two-variable separable rank.** Over any Hausdorff topological field,
if `F i` eventually has two-coordinate separable rank at most `r` and converges pointwise along a
nontrivial filter `l` to `K`, then `separableRank K ≤ r`. -/
theorem separableRank_fin2_le_of_tendsto {𝕜 α ι : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [T2Space 𝕜] {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 2 → α) → 𝕜} {K : (Fin 2 → α) → 𝕜} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ z, Filter.Tendsto (fun i => F i z) l (𝓝 (K z))) :
    separableRank K ≤ (r : ℕ) := by
  by_contra hnot_le
  have hnot_prod : ¬ IsSumOfProducts K r := fun hK => hnot_le (iInf₂_le r hK)
  obtain ⟨x, y, hdet_ne⟩ :=
    exists_submatrix_det_ne_zero_of_not_isSumOfProducts hnot_prod (r + 1) le_rfl
  let M (G : (Fin 2 → α) → 𝕜) : Matrix (Fin (r + 1)) (Fin (r + 1)) 𝕜 :=
    Matrix.of fun p q => G (fin2Vec (x q) (y p))
  have hdet_tend : Filter.Tendsto (fun i => (M (F i)).det) l (𝓝 (M K).det) := by
    have hM_t : Filter.Tendsto (fun i => M (F i)) l (𝓝 (M K)) :=
      tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => htend (fin2Vec (x q) (y p))
    exact (Continuous.matrix_det continuous_id).continuousAt.tendsto.comp hM_t
  have hdet_zero : ∀ᶠ i in l, (M (F i)).det = 0 := by
    filter_upwards [hrank] with i hi
    have hex : ∃ N ≤ r, IsSumOfProducts (F i) N := by
      by_contra hno
      push Not at hno
      have hgt : ((r : ℕ) : ℕ∞) < separableRank (F i) := by
        have hle : ((r + 1 : ℕ) : ℕ∞) ≤ separableRank (F i) :=
          le_iInf₂ fun N hN => by
            have : r < N := lt_of_not_ge fun hNr => hno N hNr hN
            exact_mod_cast Nat.succ_le_of_lt this
        exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self r) hle
      exact not_lt_of_ge hi hgt
    obtain ⟨N, hNr, hprodN⟩ := hex
    obtain ⟨f, hf⟩ := isSumOfProducts_mono hNr hprodN
    let U : Matrix (Fin (r + 1)) (Fin r) 𝕜 := Matrix.of fun p k => f k 1 (y p)
    let V : Matrix (Fin r) (Fin (r + 1)) 𝕜 := Matrix.of fun k q => f k 0 (x q)
    have hfac : M (F i) = U * V := by
      ext p q
      simp only [M, U, V, Matrix.of_apply, Matrix.mul_apply, hf, Fin.prod_univ_two,
        fin2Vec_zero, fin2Vec_one]
      refine Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hfac]
    exact det_mul_eq_zero_of_lt U V
  have hzero_lim : Filter.Tendsto (fun i => (M (F i)).det) l (𝓝 0) :=
    tendsto_const_nhds.congr' (hdet_zero.mono fun _ h => h.symm)
  exact hdet_ne (tendsto_nhds_unique hdet_tend hzero_lim)

/-- **Two-variable slice border-rank lower bound in `d ≥ 2` dimensions.** -/
theorem separableRank_padTwo_le_of_tendsto {𝕜 α ι : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [T2Space 𝕜] [Zero α] {d : ℕ} (hd : 2 ≤ d)
    {l : Filter ι} [l.NeBot] {F : ι → (Fin d → α) → 𝕜} {K : (Fin d → α) → 𝕜} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (K x))) :
    separableRank (fun y : Fin 2 → α => K (padTwo y)) ≤ (r : ℕ) := by
  refine separableRank_fin2_le_of_tendsto (F := fun i y => F i (padTwo y)) ?_
    (fun y => htend (padTwo y))
  filter_upwards [hrank] with i hi
  exact (separableRank_padTwo_le hd (F i)).trans hi

private lemma sum_padTwo_sq {d : ℕ} (hd : 2 ≤ d) (y : Fin 2 → ℝ) :
    (∑ j : Fin d, (padTwo y j) ^ 2) = ∑ j : Fin 2, y j ^ 2 := by
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin d => (j : ℕ) < 2) (fun j => (padTwo y j) ^ 2)).symm
  have hrest : ∑ j ∈ Finset.univ.filter (fun j : Fin d => ¬ (j : ℕ) < 2),
      (padTwo y j) ^ 2 = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hj' : ¬ (j : ℕ) < 2 := (Finset.mem_filter.mp hj).2
      simp [padTwo, hj']
  have htwo : ∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℕ) < 2),
      (padTwo y j) ^ 2 = ∑ j : Fin 2, y j ^ 2 := by
    have hset : Finset.univ.filter (fun j : Fin d => (j : ℕ) < 2) =
        {Fin.castLE hd 0, Fin.castLE hd 1} := by
      ext ⟨j, hj⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE, Fin.val_zero, Fin.val_one]
      omega
    have hne : Fin.castLE hd 0 ≠ Fin.castLE hd 1 := by simp [Fin.ext_iff]
    rw [hset, Finset.sum_pair hne, Fin.sum_univ_two]
    simp [padTwo, Fin.castLE]
  rw [hsplit, hrest, htwo, add_zero]

/-- **General `d`-D real border-rank lower bound (`d ≥ 2`).** Every family `F i` converging
pointwise along a nontrivial filter to `x ↦ profile cs (∑ j, x j ^ 2)` for a representation `cs`
eventually cannot have separable rank strictly below `totalCost cs` (its 2-D rank). -/
theorem totalCost_le_of_tendsto_radial_profile {d : ℕ} (hd : 2 ≤ d)
    {cs : List Component} (hcs : IsRepresentation cs)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℝ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (profile cs (∑ j, x j ^ 2)))) :
    totalCost cs ≤ r := by
  have hle := separableRank_padTwo_le_of_tendsto hd hrank htend
  have hpad : (fun y : Fin 2 → ℝ => profile cs (∑ j : Fin d, (padTwo y j) ^ 2)) =
      fun y : Fin 2 → ℝ => profile cs (∑ j : Fin 2, y j ^ 2) :=
    funext fun y => by rw [sum_padTwo_sq hd y]
  rw [hpad, separableRank_radial_two_profile hcs] at hle
  exact_mod_cast hle

/-- **Exact `d`-D complex border-rank lower bound (`d ≥ 2`).** Every family `F i` of complex
kernels on `ℝ^d` converging pointwise along a nontrivial filter to
`x ↦ ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)` (with `P μ ≠ 0` for `μ ∈ S`) eventually cannot have
separable rank strictly below `∑ μ ∈ S, ((P μ).natDegree + 1)`. -/
theorem sum_natDegree_add_one_le_of_tendsto_radial_complex {d : ℕ} (hd : 2 ≤ d)
    {S : Finset ℂ} {P : ℂ → ℂ[X]} (hP : ∀ μ ∈ S, P μ ≠ 0)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℂ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l
      (𝓝 (∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)))) :
    (∑ μ ∈ S, ((P μ).natDegree + 1)) ≤ r := by
  have hle := separableRank_padTwo_le_of_tendsto hd hrank htend
  have hpad : (fun y : Fin 2 → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j : Fin d, (padTwo y j) ^ 2)) =
      fun y : Fin 2 → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j : Fin 2, y j ^ 2) :=
    funext fun y => by rw [sum_padTwo_sq hd y]
  have hcont : ContinuousOn (fun s : ℝ => ∑ μ ∈ S, expPoly (P μ) μ s) (Set.Ici 0) := by
    refine Continuous.continuousOn ?_
    have hterm (μ : ℂ) : Continuous (fun s : ℝ => expPoly (P μ) μ s) := by
      unfold expPoly
      exact ((P μ).continuous_aeval.comp Complex.continuous_ofReal).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    fun_prop
  have h2d : separableRank (fun y : Fin 2 → ℝ =>
      ∑ μ ∈ S, expPoly (P μ) μ (∑ j : Fin 2, y j ^ 2)) =
      ((∑ μ ∈ S, ((P μ).natDegree + 1) : ℕ) : ℕ∞) := by
    rw [separableRank_radial_complex_eq_iff (le_refl 2) _ hcont]
    exact ⟨S, P, hP, fun _ _ => rfl, by simp⟩
  rw [hpad, h2d] at hle
  exact_mod_cast hle

/-- **Exact `d`-D complex border-rank upper bound (`d ≥ 2`).** For every finite set of rates `S`
and polynomials `P : ℂ → ℂ[X]`, there exists an explicit family `F h` of complex kernels on `ℝ^d`
having `d`-way separable rank at most `∑ μ ∈ S, ((P μ).natDegree + 1)` for every `h ∈ ℝ` and
converging uniformly on every compact subset `C ⊆ ℝ^d` to
`x ↦ ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)` as `h → 0` (`h ≠ 0`). Together with
`sum_natDegree_add_one_le_of_tendsto_radial_complex`, the pointwise and compact-open complex border
rank of any radial exponential polynomial equals `∑ μ ∈ S, ((P μ).natDegree + 1)` (when `P μ ≠ 0`
on `S`). -/
theorem exists_rank_le_sum_natDegree_add_one_tendstoUniformlyOn_radial_complex
    {d : ℕ} (hd : 2 ≤ d) (S : Finset ℂ) (P : ℂ → ℂ[X]) :
    ∃ F : ℝ → (Fin d → ℝ) → ℂ,
      (∀ h, separableRank (F h) ≤ (∑ μ ∈ S, ((P μ).natDegree + 1) : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty (Fin d)›
  let Fμ (μ : ℂ) (h : ℝ) (x : Fin d → ℝ) : ℂ :=
    (P μ).eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
      exp (μ * (∑ j, x j ^ 2 : ℝ))
  have hFμ_prod (μ : ℂ) (h : ℝ) : IsSumOfProducts (Fμ μ h) ((P μ).natDegree + 1) := by
    let k := (P μ).natDegree
    let L_C : ℂ[X] := Polynomial.C (-(h : ℂ)⁻¹) + Polynomial.C ((h : ℂ)⁻¹) * Polynomial.X
    have hLC_deg : L_C.natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
      simpa using (Polynomial.natDegree_C_mul_X_pow_le ((h : ℂ)⁻¹) 1)
    let Q_C : ℂ[X] := (P μ).comp L_C
    have hQC_deg : Q_C.natDegree < k + 1 := by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_comp_le.trans ?_)
      exact (Nat.mul_le_mul le_rfl hLC_deg).trans (by simp [k])
    refine ⟨fun m j u =>
      (if j = i₀ then Q_C.coeff m else 1) *
        exp ((μ + (m : ℕ) * (h : ℂ)) * (u ^ 2 : ℝ)), fun x => ?_⟩
    dsimp only [Fμ]
    set s := ∑ j : Fin d, x j ^ 2
    let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
    have hLC_eval : L_C.eval (exp ((h : ℂ) * (s : ℂ))) = (u_s : ℂ) := by
      simp only [L_C, u_s, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, ← Complex.ofReal_mul]
      rw [← Complex.ofReal_exp]
      push_cast
      ring
    rw [← hLC_eval, ← Polynomial.eval_comp, Polynomial.eval_eq_sum_range' hQC_deg,
      ← Fin.sum_univ_eq_sum_range (fun m => Q_C.coeff m * exp ((h : ℂ) * (s : ℂ)) ^ m) (k + 1),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hprod : (∏ j : Fin d,
        (if j = i₀ then Q_C.coeff m else 1) *
          exp ((μ + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ))) =
        Q_C.coeff m * ∏ j : Fin d, exp ((μ + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then Q_C.coeff m else (1 : ℂ)) = 1 :=
        Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
      simp [her]
    rw [hprod, ← Complex.exp_sum, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    have hs_cast : (∑ j : Fin d, (μ + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) =
        (μ + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by
      rw [← Finset.mul_sum]
      push_cast [s]
      rfl
    rw [hs_cast]
    have : (m : ℕ) * ((h : ℂ) * (s : ℂ)) + μ * (s : ℂ) =
        (μ + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by ring
    rw [this]
  refine ⟨fun h x => ∑ μ ∈ S, Fμ μ h x, fun h => ?_, fun C hC => ?_⟩
  · have hsum := IsSumOfProducts.finsetSum (α := S)
      (K := fun μ : S => Fμ μ.1 h) (N := fun μ : S => (P μ.1).natDegree + 1)
      (fun μ => hFμ_prod μ.1 h)
    have hfun : (fun x : Fin d → ℝ => ∑ μ : S, Fμ μ.1 h x) = fun x => ∑ μ ∈ S, Fμ μ h x := by
      funext x
      exact Finset.sum_coe_sort S (fun μ => Fμ μ h x)
    have hcost : (∑ μ : S, ((P μ.1).natDegree + 1)) = ∑ μ ∈ S, ((P μ).natDegree + 1) :=
      Finset.sum_coe_sort S (fun μ => (P μ).natDegree + 1)
    rw [hfun, hcost] at hsum
    exact iInf₂_le _ hsum
  · have hμ_tend (μ : ℂ) : TendstoUniformlyOn (Fμ μ)
        (fun x : Fin d → ℝ => expPoly (P μ) μ (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hcontS : Continuous (fun x : Fin d → ℝ => ∑ j : Fin d, x j ^ 2) := by fun_prop
      obtain ⟨B, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, ∑ j : Fin d, x j ^ 2 ≤ B := by
        rcases C.eq_empty_or_nonempty with rfl | hne
        · exact ⟨0, le_rfl, by simp⟩
        · obtain ⟨x₀, _, hmax⟩ := hC.exists_isMaxOn hne hcontS.continuousOn
          exact ⟨∑ j : Fin d, x₀ j ^ 2,
            Finset.sum_nonneg fun j _ => sq_nonneg (x₀ j), fun x hx => hmax hx⟩
      let g (p : ℝ × ℝ) : ℂ := (P μ).eval (p.1 : ℂ) * exp (μ * (p.2 : ℂ))
      have hg_cont : Continuous g :=
        ((P μ).continuous_aeval.comp (Complex.continuous_ofReal.comp continuous_fst)).mul
          (Complex.continuous_exp.comp
            (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
      let K_box : Set (ℝ × ℝ) := Set.Icc (-1) (B + 1) ×ˢ Set.Icc 0 B
      obtain ⟨δ_u, hδ_u_pos, hδ_u⟩ := Metric.uniformContinuousOn_iff.mp
        ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hg_cont.continuousOn)
        ε hε
      let M_B : ℝ := max 1 ((B + 1) ^ 2 * Real.exp (B + 1))
      have hM_B_pos : 0 < M_B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      let η : ℝ := min 1 (min δ_u 1 / (2 * M_B))
      have hη_pos : 0 < η :=
        lt_min zero_lt_one (div_pos (lt_min hδ_u_pos zero_lt_one) (mul_pos zero_lt_two hM_B_pos))
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hη_pos)] with h hh0 hball x hxC
      have hhη : |h| < η := by simpa [Real.dist_eq] using hball
      set s := ∑ j : Fin d, x j ^ 2
      have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
      have hsB : s ≤ B := hB.2 x hxC
      have hh1 : |h| ≤ 1 := le_of_lt (lt_of_lt_of_le hhη (min_le_left _ _))
      let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
      have hu_diff : |u_s - s| < min δ_u 1 := by
        have hh0' : h ≠ 0 := hh0
        have hh_pos : 0 < |h| := abs_pos.mpr hh0'
        have hsub : u_s - s = h⁻¹ * (Real.exp (h * s) - 1 - h * s) := by
          dsimp only [u_s]; field_simp [hh0']
        have habs_hs : |h * s| ≤ B + 1 := by
          rw [abs_mul, abs_of_nonneg hs0]; nlinarith
        have hexp_b := abs_exp_sub_one_sub_le (h * s)
        have hrem : |u_s - s| ≤ |h| * M_B := by
          rw [hsub, abs_mul, abs_inv]
          calc
            |h|⁻¹ * |Real.exp (h * s) - 1 - h * s|
                ≤ |h|⁻¹ * ((h * s) ^ 2 * Real.exp |h * s|) := by gcongr
            _ = |h| * (s ^ 2 * Real.exp |h * s|) := by
                have : (h * s) ^ 2 = |h| * |h| * s ^ 2 := by rw [mul_pow, ← sq_abs h, sq]
                rw [this]; field_simp [hh_pos.ne']
            _ ≤ |h| * ((B + 1) ^ 2 * Real.exp (B + 1)) := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
                exact mul_le_mul (pow_le_pow_left₀ hs0 (by linarith) 2)
                  (Real.exp_le_exp.mpr habs_hs) (Real.exp_pos _).le (sq_nonneg _)
            _ ≤ |h| * M_B := mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg h)
        calc
          |u_s - s| ≤ |h| * M_B := hrem
          _ < η * M_B := mul_lt_mul_of_pos_right hhη hM_B_pos
          _ ≤ (min δ_u 1 / (2 * M_B)) * M_B :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hM_B_pos.le
          _ = min δ_u 1 / 2 := by field_simp [hM_B_pos.ne']
          _ < min δ_u 1 := half_lt_self (lt_min hδ_u_pos zero_lt_one)
      have hu_box : (u_s, s) ∈ K_box := by
        have hu1 : |u_s - s| ≤ 1 := le_of_lt (lt_of_lt_of_le hu_diff (min_le_right _ _))
        rw [abs_le] at hu1
        exact ⟨⟨by linarith, by linarith⟩, ⟨hs0, hsB⟩⟩
      have hs_box : (s, s) ∈ K_box := ⟨⟨by linarith, by linarith⟩, ⟨hs0, hsB⟩⟩
      have hdist : dist (s, s) (u_s, s) < δ_u := by
        rw [Prod.dist_eq]
        simp only [dist_self, max_eq_left dist_nonneg]
        rw [Real.dist_eq, abs_sub_comm]
        exact lt_of_lt_of_le hu_diff (min_le_left _ _)
      exact hδ_u (s, s) hs_box (u_s, s) hu_box hdist
    clear * - hμ_tend
    induction S using Finset.cons_induction with
    | empty =>
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε
    | cons μ S hnot ih =>
      simp_rw [Finset.sum_cons]
      exact (hμ_tend μ).add ih

end LowerSemicontinuity

section AdjugateBorderRank

/-- **Polynomial adjugate trace obstruction to real border rank `≤ n` in 3-D.**
For any 3-way real function `G` of separable rank at most `n` and any evaluation points
`u₀, u₁` and `p, q : Fin n → X`, the two `n × n` mode-0 slices
`S₀ a b = G ![u₀, p a, q b]` and `S₁ a b = G ![u₁, p a, q b]` satisfy
`0 ≤ trace ((adjugate S₀ * S₁) ^ 2)`. -/
private lemma trace_adjugate_mul_sq_nonneg_of_isSumOfProducts {X : Type*} {n : ℕ}
    {G : (Fin 3 → X) → ℝ} (hG : IsSumOfProducts G n) (u₀ u₁ : X) (p q : Fin n → X) :
    0 ≤ (((Matrix.of fun a b => G ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => G ![u₁, p a, q b]) *
        ((Matrix.of fun a b => G ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => G ![u₁, p a, q b])).trace := by
  obtain ⟨f, hf⟩ := hG
  let V : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a k => f k 1 (p a)
  let W : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k b => f k 2 (q b)
  let d₀ : Fin n → ℝ := fun k => f k 0 u₀
  let d₁ : Fin n → ℝ := fun k => f k 0 u₁
  let D₀ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d₀
  let D₁ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d₁
  have hS₀ : (Matrix.of fun a b => G ![u₀, p a, q b]) = V * D₀ * W := by
    ext a b
    dsimp only [D₀, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, V, W, d₀, Matrix.of_apply, hf, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hS₁ : (Matrix.of fun a b => G ![u₁, p a, q b]) = V * D₁ * W := by
    ext a b
    dsimp only [D₁, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, V, W, d₁, Matrix.of_apply, hf, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hS₀, hS₁]
  let c : Fin n → ℝ := fun k => (∏ j ∈ Finset.univ.erase k, d₀ j) * d₁ k
  have hD_adj : D₀.adjugate * D₁ = Matrix.diagonal c := by
    rw [Matrix.adjugate_diagonal, Matrix.diagonal_mul_diagonal]
  have hprod : (V * D₀ * W).adjugate * (V * D₁ * W) =
      V.det • (W.adjugate * Matrix.diagonal c * W) := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    have hassoc : W.adjugate * (D₀.adjugate * V.adjugate) * (V * D₁ * W) =
        W.adjugate * D₀.adjugate * (V.adjugate * V) * D₁ * W := by
      simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.adjugate_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.smul_mul_assoc, mul_one, Matrix.mul_assoc W.adjugate D₀.adjugate D₁, hD_adj]
  rw [hprod, smul_mul_smul_comm]
  have hsq : (W.adjugate * Matrix.diagonal c * W) * (W.adjugate * Matrix.diagonal c * W) =
      W.det • (W.adjugate * Matrix.diagonal (fun k => c k * c k) * W) := by
    have hassoc : (W.adjugate * Matrix.diagonal c * W) * (W.adjugate * Matrix.diagonal c * W) =
        W.adjugate * Matrix.diagonal c * (W * W.adjugate) * Matrix.diagonal c * W := by
      simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.mul_adjugate, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.smul_mul_assoc, mul_one, Matrix.mul_assoc W.adjugate, Matrix.diagonal_mul_diagonal]
  rw [hsq, smul_smul, Matrix.trace_smul]
  have htr : (W.adjugate * Matrix.diagonal (fun k => c k * c k) * W).trace =
      W.det * ∑ k : Fin n, c k * c k := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_adjugate, Algebra.smul_mul_assoc,
      one_mul, Matrix.trace_smul, Matrix.trace_diagonal, smul_eq_mul]
  rw [htr, smul_eq_mul]
  have h1 : (V.det * V.det * W.det) * (W.det * ∑ k : Fin n, c k * c k) =
      (V.det * W.det) ^ 2 * ∑ k : Fin n, c k ^ 2 := by
    have hsum : (∑ k : Fin n, c k * c k) = ∑ k : Fin n, c k ^ 2 :=
      Finset.sum_congr rfl fun k _ => (sq (c k)).symm
    rw [hsum]
    ring
  rw [h1]
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)

private lemma not_exists_rank_le_tendsto_of_trace_adjugate_neg {X ι : Type*} {n : ℕ}
    {l : Filter ι} [l.NeBot] {F : ι → (Fin 3 → X) → ℝ} {K : (Fin 3 → X) → ℝ}
    (u₀ u₁ : X) (p q : Fin n → X)
    (hneg : (((Matrix.of fun a b => K ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => K ![u₁, p a, q b]) *
        ((Matrix.of fun a b => K ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => K ![u₁, p a, q b])).trace < 0)
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (n : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (K x))) : False := by
  let S₀ (G : (Fin 3 → X) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun a b => G ![u₀, p a, q b]
  let S₁ (G : (Fin 3 → X) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun a b => G ![u₁, p a, q b]
  let Φ (G : (Fin 3 → X) → ℝ) : ℝ := ((S₀ G).adjugate * S₁ G * ((S₀ G).adjugate * S₁ G)).trace
  have hΦ_tend : Filter.Tendsto (fun i => Φ (F i)) l (𝓝 (Φ K)) := by
    have hS₀_t : Filter.Tendsto (fun i => S₀ (F i)) l (𝓝 (S₀ K)) :=
      tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => htend ![u₀, p a, q b]
    have hS₁_t : Filter.Tendsto (fun i => S₁ (F i)) l (𝓝 (S₁ K)) :=
      tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => htend ![u₁, p a, q b]
    have hadj_cont : Continuous
        (Matrix.adjugate : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [Matrix.adjugate_apply]
      refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
      by_cases h : i = b
      · subst h; simp only [Matrix.updateRow_self]; fun_prop
      · simp only [Matrix.updateRow_ne h]
        exact (continuous_apply j).comp (continuous_apply i)
    have hM_t : Filter.Tendsto (fun i => (S₀ (F i)).adjugate * S₁ (F i)) l
        (𝓝 ((S₀ K).adjugate * S₁ K)) :=
      (hadj_cont.continuousAt.tendsto.comp hS₀_t).mul hS₁_t
    have hsq_t := hM_t.mul hM_t
    have htr_cont : Continuous (Matrix.trace : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
      unfold Matrix.trace Matrix.diag
      fun_prop
    exact htr_cont.continuousAt.tendsto.comp hsq_t
  have hΦ_nonneg : ∀ᶠ i in l, 0 ≤ Φ (F i) := by
    filter_upwards [hrank] with i hi
    have hex : ∃ N ≤ n, IsSumOfProducts (F i) N := by
      by_contra hno
      push Not at hno
      have hgt : ((n : ℕ) : ℕ∞) < separableRank (F i) := by
        have hle : ((n + 1 : ℕ) : ℕ∞) ≤ separableRank (F i) :=
          le_iInf₂ fun N hN => by
            have : n < N := lt_of_not_ge fun hNn => hno N hNn hN
            exact_mod_cast Nat.succ_le_of_lt this
        exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle
      exact not_lt_of_ge hi hgt
    obtain ⟨N, hNn, hprodN⟩ := hex
    exact trace_adjugate_mul_sq_nonneg_of_isSumOfProducts (isSumOfProducts_mono hNn hprodN)
      u₀ u₁ p q
  exact not_lt_of_ge (ge_of_tendsto hΦ_tend hΦ_nonneg) hneg

/-- **Sharpness of `B_3 = 3` for a pure nonreal Gaussian on `ℝ³`.** No family of real kernels of
separable rank at most `2` converges even pointwise along a nontrivial filter to `cos(‖x‖²)` on
`ℝ³`. Since `separableRank (x ↦ cos(‖x‖²)) = 3`, its pointwise and compact-open real border rank
is `3`. -/
theorem not_exists_rank_le_two_tendsto_radial_cos {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 3 → ℝ) → ℝ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (2 : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (Real.cos (∑ j, x j ^ 2)))) : False := by
  let r : ℝ := Real.sqrt (Real.pi / 2)
  have hr_sq : r ^ 2 = Real.pi / 2 := Real.sq_sqrt (by positivity)
  let p : Fin 2 → ℝ := ![0, r]
  refine not_exists_rank_le_tendsto_of_trace_adjugate_neg 0 r p p ?_ hrank htend
  have hS₀ : (Matrix.of fun a b : Fin 2 => Real.cos (∑ j : Fin 3, (![0, p a, p b] j) ^ 2)) =
      !![(1 : ℝ), 0; 0, -1] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [p, Fin.sum_univ_three, hr_sq, add_halves, Real.cos_pi_div_two, Real.cos_pi]
  have hc3pi : Real.cos (Real.pi + Real.pi / 2) = 0 := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hS₁ : (Matrix.of fun a b : Fin 2 => Real.cos (∑ j : Fin 3, (![r, p a, p b] j) ^ 2)) =
      !![(0 : ℝ), -1; -1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [p, Fin.sum_univ_three, hr_sq, add_halves, Real.cos_pi_div_two, Real.cos_pi, hc3pi]
  rw [hS₀, hS₁, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- **Pointwise real border-rank lower bound `≥ 5` for `‖x‖² cos(‖x‖²)` on `ℝ³`.**
No family of real kernels on `ℝ³` of separable rank at most `4` can converge pointwise along a
nontrivial filter to `‖x‖² cos(‖x‖²)`. -/
theorem not_exists_rank_le_four_tendsto_radial_sq_mul_cos {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 3 → ℝ) → ℝ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (4 : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l
      (𝓝 ((∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)))) : False := by
  obtain ⟨h, hh_eq⟩ : ∃ h : ℝ, h = Real.pi / 2 := ⟨Real.pi / 2, rfl⟩
  have hh_pos : 0 < h := by rw [hh_eq]; positivity
  let p : Fin 4 → ℝ := ![0, Real.sqrt h, Real.sqrt (2 * h), Real.sqrt (3 * h)]
  refine not_exists_rank_le_tendsto_of_trace_adjugate_neg 0 (Real.sqrt h) p p ?_ hrank htend
  have hs1 : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh_pos.le
  have hs2 : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  have hs3 : Real.sqrt (3 * h) ^ 2 = 3 * h := Real.sq_sqrt (by positivity)
  have hc1 : Real.cos h = 0 := by rw [hh_eq]; exact Real.cos_pi_div_two
  have hc2 : Real.cos (2 * h) = -1 := by
    have : 2 * h = Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_pi]
  have hc3 : Real.cos (3 * h) = 0 := by
    have : 3 * h = Real.pi + Real.pi / 2 := by rw [hh_eq]; ring
    rw [this, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hc4 : Real.cos (4 * h) = 1 := by
    have : 4 * h = 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_two_pi]
  have hc5 : Real.cos (5 * h) = 0 := by
    have : 5 * h = h + 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_add_two_pi, hc1]
  have hc6 : Real.cos (6 * h) = -1 := by
    have : 6 * h = 2 * h + 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_add_two_pi, hc2]
  have hc7 : Real.cos (7 * h) = 0 := by
    have : 7 * h = 3 * h + 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_add_two_pi, hc3]
  have hc2' : Real.cos (h * 2) = -1 := by rw [mul_comm, hc2]
  have hc3' : Real.cos (h * 3) = 0 := by rw [mul_comm, hc3]
  have hc4' : Real.cos (h * 4) = 1 := by rw [mul_comm, hc4]
  have hc5' : Real.cos (h * 5) = 0 := by rw [mul_comm, hc5]
  have hc6' : Real.cos (h * 6) = -1 := by rw [mul_comm, hc6]
  have hc7' : Real.cos (h * 7) = 0 := by rw [mul_comm, hc7]
  let A₀R : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0, 0, -2, 0;
       0, -2, 0, 4;
       -2, 0, 4, 0;
       0, 4, 0, -6]
  let A₁R : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0, -2, 0, 4;
       -2, 0, 4, 0;
       0, 4, 0, -6;
       4, 0, -6, 0]
  let B₀R : Matrix (Fin 4) (Fin 4) ℝ :=
    !![-16, 0, -8, 0;
       0, 24, 0, 16;
       -8, 0, 0, 0;
       0, 16, 0, 8]
  have heval (u : ℝ) (a b : Fin 4) :
      (∑ j : Fin 3, (![u, p a, p b] j) ^ 2) *
        Real.cos (∑ j : Fin 3, (![u, p a, p b] j) ^ 2) =
      (u ^ 2 + p a ^ 2 + p b ^ 2) * Real.cos (u ^ 2 + p a ^ 2 + p b ^ 2) := by
    simp [Fin.sum_univ_three, add_assoc]
  have hS₀ : (Matrix.of fun a b : Fin 4 =>
      (∑ j : Fin 3, (![0, p a, p b] j) ^ 2) *
        Real.cos (∑ j : Fin 3, (![0, p a, p b] j) ^ 2)) = h • A₀R := by
    ext a b
    rw [Matrix.of_apply, heval, show (0 : ℝ) ^ 2 = 0 by ring, zero_add]
    fin_cases a <;> fin_cases b <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk];
       dsimp only [p, A₀R];
       rw [Matrix.smul_apply, smul_eq_mul];
       simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons];
       (repeat rw [show (0 : ℝ) ^ 2 = 0 by ring]);
       (repeat rw [hs1]); (repeat rw [hs2]); (repeat rw [hs3]);
       (try ring_nf);
       (try rw [hc1]); (try rw [hc2']); (try rw [hc3']);
       (try rw [hc4']); (try rw [hc5']); (try rw [hc6']);
       (try ring))
  have hS₁ : (Matrix.of fun a b : Fin 4 =>
      (∑ j : Fin 3, (![Real.sqrt h, p a, p b] j) ^ 2) *
        Real.cos (∑ j : Fin 3, (![Real.sqrt h, p a, p b] j) ^ 2)) = h • A₁R := by
    ext a b
    rw [Matrix.of_apply, heval, Real.sq_sqrt hh_pos.le]
    fin_cases a <;> fin_cases b <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk];
       dsimp only [p, A₁R];
       rw [Matrix.smul_apply, smul_eq_mul];
       simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons];
       (repeat rw [show (0 : ℝ) ^ 2 = 0 by ring]);
       (repeat rw [hs1]); (repeat rw [hs2]); (repeat rw [hs3]);
       (try ring_nf);
       (try rw [hc1]); (try rw [hc2']); (try rw [hc3']); (try rw [hc4']);
       (try rw [hc5']); (try rw [hc6']); (try rw [hc7']);
       (try ring))
  have hBA : B₀R * A₀R = (16 : ℝ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B₀R, A₀R, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  have hdetA : A₀R.det = 16 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp [A₀R, Matrix.submatrix_apply, Fin.succAbove, Matrix.det_fin_three]
    norm_num
  have hadjA : A₀R.adjugate = B₀R := by
    have h1 : (16 : ℝ) • A₀R.adjugate = (16 : ℝ) • B₀R := by
      calc
        (16 : ℝ) • A₀R.adjugate = ((16 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) * A₀R.adjugate := by
          rw [Algebra.smul_mul_assoc, one_mul]
        _ = (B₀R * A₀R) * A₀R.adjugate := by rw [← hBA]
        _ = B₀R * (A₀R * A₀R.adjugate) := Matrix.mul_assoc _ _ _
        _ = B₀R * (A₀R.det • 1) := by rw [Matrix.mul_adjugate]
        _ = (16 : ℝ) • B₀R := by rw [hdetA, Algebra.mul_smul_comm, mul_one]
    exact smul_right_injective _ (by norm_num : (16 : ℝ) ≠ 0) h1
  have hmap : ((A₀R.adjugate * A₁R) * (A₀R.adjugate * A₁R)).trace = (-1024 : ℝ) := by
    rw [hadjA]
    simp only [B₀R, A₁R, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    norm_num
  rw [hS₀, hS₁, Matrix.adjugate_smul]
  simp only [Fintype.card_fin]
  have hsmul_prod :
      (h ^ (4 - 1) • A₀R.adjugate * h • A₁R) = (h ^ 3 * h) • (A₀R.adjugate * A₁R) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [hsmul_prod, smul_mul_smul_comm, Matrix.trace_smul, hmap, smul_eq_mul]
  have hpow : 0 < (h ^ 3 * h) * (h ^ 3 * h) := by positivity
  nlinarith

/-- **Non-Gaussian border-rank upper bound `≤ 5 < B_3 = 6` for `‖x‖² cos(‖x‖²)` on `ℝ³`.**
There exists an explicit family `F h` of real separable kernels of rank at most `5` on `ℝ³`
converging uniformly on every compact subset `C ⊆ ℝ³` to `‖x‖² cos(‖x‖²)` as `h → 0` (`h ≠ 0`).
Together with `not_exists_rank_le_four_tendsto_radial_sq_mul_cos`, the exact pointwise and
compact-open real border rank of `‖x‖² cos(‖x‖²)` on `ℝ³` is `5`, strictly below both its exact
real rank `C_3 = 7` and the radial multi-Gaussian border-rank bound `B_3 = 6`. -/
theorem exists_rank_le_five_tendstoUniformlyOn_radial_sq_mul_cos :
    ∃ F : ℝ → (Fin 3 → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (5 : ℕ)) ∧
      ∀ C : Set (Fin 3 → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by
  let r3 : ℝ := Real.sqrt 3 / 2
  let p₁ (u : ℝ) : ℝ := 1 / 2 * Real.cos (u ^ 2) - r3 * Real.sin (u ^ 2)
  let q₁ (u : ℝ) : ℝ := (u ^ 2) * p₁ u
  let p₂ (u : ℝ) : ℝ := -1 / 2 * Real.cos (u ^ 2) - r3 * Real.sin (u ^ 2)
  let q₂ (u : ℝ) : ℝ := (u ^ 2) * p₂ u
  let f1d (h : ℝ) : Fin 5 → ℝ → ℝ
    | 0, u => Real.cos (u ^ 2) + 4 * h * ((u ^ 2) * Real.cos (u ^ 2))
    | 1, u => Real.sin (u ^ 2) + h ^ 2 * Real.cos (u ^ 2)
    | 2, u => Real.sin (u ^ 2)
    | 3, u => p₁ u + h * q₁ u
    | 4, u => p₂ u + h * q₂ u
  let w (h : ℝ) : Fin 5 → ℝ
    | 0 => 1 / (3 * h)
    | 1 => 1 / h ^ 3
    | 2 => -1 / h ^ 3
    | 3 => -4 / (3 * h)
    | 4 => 4 / (3 * h)
  let fac (h : ℝ) (k : Fin 5) (j : Fin 3) (u : ℝ) : ℝ :=
    if j = 0 then w h k * f1d h k u else f1d h k u
  let F (h : ℝ) (x : Fin 3 → ℝ) : ℝ := ∑ k : Fin 5, ∏ j : Fin 3, fac h k j (x j)
  let Rem (x : Fin 3 → ℝ) (h : ℝ) : ℝ :=
    let t0 := x 0 ^ 2; let t1 := x 1 ^ 2; let t2 := x 2 ^ 2
    let c0 := Real.cos t0; let c1 := Real.cos t1; let c2 := Real.cos t2
    let s0 := Real.sin t0; let s1 := Real.sin t1; let s2 := Real.sin t2
    16 / 3 * (t0 * t1 + t0 * t2 + t1 * t2) * c0 * c1 * c2 +
      64 / 3 * h * t0 * t1 * t2 * c0 * c1 * c2 +
      (c0 * c1 * s2 + c0 * s1 * c2 + s0 * c1 * c2) +
      h ^ 2 * c0 * c1 * c2 -
      4 / 3 * (p₁ (x 0) * q₁ (x 1) * q₁ (x 2) + q₁ (x 0) * p₁ (x 1) * q₁ (x 2) +
        q₁ (x 0) * q₁ (x 1) * p₁ (x 2)) -
      4 / 3 * h * q₁ (x 0) * q₁ (x 1) * q₁ (x 2) +
      4 / 3 * (p₂ (x 0) * q₂ (x 1) * q₂ (x 2) + q₂ (x 0) * p₂ (x 1) * q₂ (x 2) +
        q₂ (x 0) * q₂ (x 1) * p₂ (x 2)) +
      4 / 3 * h * q₂ (x 0) * q₂ (x 1) * q₂ (x 2)
  have hident (h : ℝ) (hh0 : h ≠ 0) (x : Fin 3 → ℝ) :
      F h x - (∑ j : Fin 3, x j ^ 2) * Real.cos (∑ j : Fin 3, x j ^ 2) = h * Rem x h := by
    have hcos_sum : Real.cos (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) =
        Real.cos (x 0 ^ 2) * Real.cos (x 1 ^ 2) * Real.cos (x 2 ^ 2) -
          Real.cos (x 0 ^ 2) * Real.sin (x 1 ^ 2) * Real.sin (x 2 ^ 2) -
          Real.sin (x 0 ^ 2) * Real.cos (x 1 ^ 2) * Real.sin (x 2 ^ 2) -
          Real.sin (x 0 ^ 2) * Real.sin (x 1 ^ 2) * Real.cos (x 2 ^ 2) := by
      rw [Real.cos_add, Real.cos_add, Real.sin_add]
      ring
    dsimp only [F, fac, Rem, w, f1d, q₁, q₂, p₁, p₂]
    rw [Fin.sum_univ_five, Fin.sum_univ_three]
    simp only [Fin.prod_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    rw [hcos_sum]
    have hh3 : 3 * h ^ 3 ≠ 0 := by positivity
    apply mul_left_cancel₀ hh3
    field_simp [hh0]
    dsimp only [r3]
    ring_nf
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3)]
    ring
  refine ⟨F, fun h => iInf₂_le 5 ⟨fac h, fun _ => rfl⟩, fun C hC => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hRem_cont : Continuous (fun p : (Fin 3 → ℝ) × ℝ => Rem p.1 p.2) := by
    dsimp only [Rem, q₁, q₂, p₁, p₂]
    fun_prop
  obtain ⟨B, hB⟩ := (hC.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := C ×ˢ Set.Icc (-1 : ℝ) 1) hRem_cont.continuousOn
  let M : ℝ := max B 0 + 1
  have hM_pos : 0 < M := by positivity
  let δ : ℝ := min 1 (ε / M)
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hε hM_pos)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ_pos)] with h hh0 hball x hxC
  have hhδ : |h| < δ := by simpa [Real.dist_eq] using hball
  have hh1 : |h| ≤ 1 := le_of_lt (lt_of_lt_of_le hhδ (min_le_left _ _))
  have hh_in : h ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hh1
  have hRem_le : |Rem x h| ≤ M := by
    have hb : ‖Rem x h‖ ≤ B := hB (x, h) ⟨hxC, hh_in⟩
    rw [Real.norm_eq_abs] at hb
    linarith [le_max_left B 0]
  rw [Real.dist_eq, abs_sub_comm, hident h hh0 x, abs_mul]
  calc
    |h| * |Rem x h| ≤ |h| * M := mul_le_mul_of_nonneg_left hRem_le (abs_nonneg h)
    _ < δ * M := mul_lt_mul_of_pos_right hhδ hM_pos
    _ ≤ (ε / M) * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM_pos.le
    _ = ε := div_mul_cancel₀ ε hM_pos.ne'

end AdjugateBorderRank

section UniversalApproximation

private lemma sum_Icc_neg_eq_zero_add_sum_fin {α : Type*} [AddCommMonoid α] (g : ℤ → α) :
    ∀ M : ℕ, ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), g n =
      g 0 + ∑ m : Fin M, (g ((m : ℕ) + 1 : ℤ) + g (-(((m : ℕ) + 1 : ℕ) : ℤ)))
  | 0 => by simp
  | M + 1 => by
    have hset : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert ((M + 1 : ℕ) : ℤ)
          (insert (-((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot1 : -((M + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hnot2 : ((M + 1 : ℕ) : ℤ) ∉
        insert (-((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert hnot2, Finset.sum_insert hnot1,
      sum_Icc_neg_eq_zero_add_sum_fin g M, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h1 : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by push_cast; rfl
    rw [h1]
    abel

private lemma re_mul_exp_neg_I_mul (z : ℂ) (θ : ℝ) :
    (z * exp (-(I * (θ : ℂ)))).re = (star z * exp (I * (θ : ℂ))).re := by
  have h1 : exp (I * (θ : ℂ)) = Real.cos θ + Real.sin θ * I := by
    rw [mul_comm I (θ : ℂ), exp_mul_I]
    simp
  have h2 : exp (-(I * (θ : ℂ))) = Real.cos θ - Real.sin θ * I := by
    have : -(I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
    simp [sub_eq_add_neg]
  rw [h1, h2]
  simp [Complex.mul_re]

/-- **Equal-width harmonic complex-Gaussian universal approximation on `ℝ^d` (`d ≥ 2`).**
For every continuous radial profile `ψ : ℝ → ℝ` on `[0, ∞)` with `lim_{s → ∞} ψ(s) = 0`, every
shared decay parameter `α > 0`, and every tolerance `ε > 0`, there exist a fundamental frequency
`ω₀ > 0`, a harmonic count `M`, a real DC Gaussian weight `a₀`, and complex harmonic weights
`a₁, …, a_M` such that the equal-width harmonic multi-Gaussian kernel
`x ↦ a₀ exp(-α ‖x‖²) + ∑_{m=1}^M Re (a_m exp((-α + i m ω₀) ‖x‖²))`
has `d`-way real separable rank at most `1 + d M` and approximates `x ↦ ψ(‖x‖²)` uniformly
within `ε` across *all* of `ℝ^d`. -/
theorem exists_harmonic_gaussian_uniform_approx {d : ℕ} (hd : 2 ≤ d)
    {ψ : ℝ → ℝ} (hψ_cont : ContinuousOn ψ (Set.Ici 0))
    (hψ_zero : Filter.Tendsto ψ Filter.atTop (𝓝 0))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ω₀ : ℝ) (M : ℕ) (a₀ : ℝ) (a : Fin M → ℂ),
      0 < ω₀ ∧
      separableRank (fun x : Fin d → ℝ =>
        a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
          ∑ m : Fin M,
            (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (∑ j, x j ^ 2 : ℝ))).re) ≤
        (1 + d * M : ℕ) ∧
      ∀ x : Fin d → ℝ,
        |(a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
            ∑ m : Fin M,
              (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) *
                (∑ j, x j ^ 2 : ℝ))).re) -
          ψ (∑ j, x j ^ 2)| < ε := by
  let ψ₀ (s : ℝ) : ℝ := ψ (max s 0)
  have hψ₀_cont : Continuous ψ₀ :=
    hψ_cont.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hψ₀_eq (s : ℝ) (hs : 0 ≤ s) : ψ₀ s = ψ s := by simp [ψ₀, max_eq_left hs]
  obtain ⟨S₁, hS₁⟩ := Metric.tendsto_atTop.mp hψ_zero (ε / 4) (by positivity)
  let S₀ : ℝ := max S₁ 1
  have hS₀_ge1 : 1 ≤ S₀ := le_max_right S₁ 1
  have hψ_tail (s : ℝ) (hs : S₀ ≤ s) : |ψ₀ s| < ε / 4 := by
    have hs0 : 0 ≤ s := by linarith
    rw [hψ₀_eq s hs0]
    have hd_lt := hS₁ s ((le_max_left S₁ 1).trans hs)
    simpa [Real.dist_eq] using hd_lt
  have hprod_cont : Continuous (fun u : ℝ => Real.exp (α * u) * ψ₀ u) := by fun_prop
  obtain ⟨B_raw, hB_raw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc 0 (S₀ + 1)) hprod_cont.continuousOn
  let B : ℝ := max B_raw 0
  let M_bound : ℝ := max B |ψ₀ 0| + 1
  have hM_pos : 0 < M_bound := by positivity
  have hlim_exp : Filter.Tendsto (fun t : ℝ => Real.exp (-α * t) * M_bound)
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => α * t) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hα Filter.tendsto_id
    have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-α * t)) Filter.atTop (𝓝 0) := by
      have heq : (fun t : ℝ => Real.exp (-α * t)) = fun t => Real.exp (-(α * t)) := by
        funext t; ring_nf
      rw [heq]
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa using h2.mul_const M_bound
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp hlim_exp (ε / 4) (by positivity)
  let T : ℝ := max (T₁ + 1) (S₀ + 3)
  have hT_gt : S₀ + 2 < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT_pos : 0 < T := by linarith
  have _ : Fact (0 < T) := ⟨hT_pos⟩
  let ω₀ : ℝ := 2 * Real.pi / T
  have hω₀_pos : 0 < ω₀ := by positivity
  let c₁ (u : ℝ) : ℝ := max 0 (min 1 (S₀ + 1 - u))
  let c₂ (u : ℝ) : ℝ := max 0 (min 1 (u - (T - 1)))
  let g_raw (u : ℝ) : ℝ := c₁ u * (Real.exp (α * u) * ψ₀ u) + c₂ u * ψ₀ 0
  have hg_cont : Continuous g_raw := by dsimp only [g_raw, c₁, c₂]; fun_prop
  have hg_0T : (g_raw 0 : ℂ) = (g_raw T : ℂ) := by
    congr 1
    have hc1_0 : c₁ 0 = 1 := by
      dsimp only [c₁]; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    have hc2_0 : c₂ 0 = 0 := by
      dsimp only [c₂]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    have hc1_T : c₁ T = 0 := by
      dsimp only [c₁]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    have hc2_T : c₂ T = 1 := by
      dsimp only [c₂]; rw [show T - (T - 1) = 1 by ring, min_self, max_eq_right zero_le_one]
    simp [g_raw, hc1_0, hc2_0, hc1_T, hc2_T]
  let G : C(AddCircle T, ℂ) :=
    ⟨AddCircle.liftIco T 0 (fun u => (g_raw u : ℂ)),
      AddCircle.liftIco_zero_continuous hg_0T
        (Complex.continuous_ofReal.comp hg_cont).continuousOn⟩
  have hG_bound (z : AddCircle T) : |(G z).re| ≤ M_bound := by
    let u_sub := AddCircle.equivIco T 0 z
    let u : ℝ := u_sub.1
    have hu_mem : u ∈ Set.Ico 0 T := ⟨u_sub.2.1, by linarith [u_sub.2.2]⟩
    have hz_eq : (u : AddCircle T) = z := (AddCircle.equivIco T 0).symm_apply_apply z
    have hGu : G z = (g_raw u : ℂ) := by
      rw [← hz_eq]
      change AddCircle.liftIco T 0 (fun v => (g_raw v : ℂ)) (u : AddCircle T) = _
      exact AddCircle.liftIco_zero_coe_apply hu_mem
    rw [hGu, Complex.ofReal_re]
    have hu0 : 0 ≤ u := hu_mem.1
    by_cases huS : u ≤ S₀ + 1
    · have hc2_z : c₂ u = 0 := by
        dsimp only [c₂]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hc1_b : |c₁ u| ≤ 1 := by
        dsimp only [c₁]
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one (min_le_left _ _)
      have hBb : |Real.exp (α * u) * ψ₀ u| ≤ B := by
        have hb := hB_raw u ⟨hu0, huS⟩
        rw [Real.norm_eq_abs] at hb
        exact hb.trans (le_max_left _ _)
      have hterm : |g_raw u| ≤ B := by
        dsimp only [g_raw]
        rw [hc2_z, zero_mul, add_zero, abs_mul]
        calc
          |c₁ u| * |Real.exp (α * u) * ψ₀ u| ≤ 1 * B :=
            mul_le_mul hc1_b hBb (abs_nonneg _) zero_le_one
          _ = B := one_mul B
      exact hterm.trans ((le_max_left B |ψ₀ 0|).trans (by linarith))
    · have hc1_z : c₁ u = 0 := by
        dsimp only [c₁]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hc2_b : |c₂ u| ≤ 1 := by
        dsimp only [c₂]
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one (min_le_left _ _)
      have hterm : |g_raw u| ≤ |ψ₀ 0| := by
        dsimp only [g_raw]
        rw [hc1_z, zero_mul, zero_add, abs_mul]
        calc
          |c₂ u| * |ψ₀ 0| ≤ 1 * |ψ₀ 0| :=
            mul_le_mul_of_nonneg_right hc2_b (abs_nonneg _)
          _ = |ψ₀ 0| := one_mul _
      exact hterm.trans ((le_max_right B |ψ₀ 0|).trans (by linarith))
  have hG_mem : G ∈ (Submodule.span ℂ (Set.range (fourier (T := T)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨P_trig, hP_span, hGP_dist⟩ :=
    Metric.mem_closure_iff.mp hG_mem (ε / 4) (by positivity)
  obtain ⟨c, hc_eq⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hP_span
  let M : ℕ := c.support.sup Int.natAbs
  let a₀ : ℝ := (c 0).re
  let a (m : Fin M) : ℂ := c ((m : ℕ) + 1 : ℤ) + star (c (-(((m : ℕ) + 1 : ℕ) : ℤ)))
  have htrig_re (s : ℝ) : (P_trig (s : AddCircle T)).re =
      a₀ + ∑ m : Fin M, (a m * exp (I * ((((m : ℕ) + 1 : ℝ) * ω₀) * (s : ℂ)))).re := by
    have hP_eval : P_trig (s : AddCircle T) =
        ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), c n * fourier (T := T) n (s : AddCircle T) := by
      rw [← hc_eq]
      change (∑ n ∈ c.support, (c n • fourier (T := T) n)) (s : AddCircle T) = _
      rw [ContinuousMap.coe_sum, Finset.sum_apply]
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_subset (fun n hn => ?_) (fun n _ hn => ?_)
      · have hle : n.natAbs ≤ M := Finset.le_sup hn
        rw [Finset.mem_Icc]
        omega
      · have hcz : c n = 0 := Finsupp.notMem_support_iff.mp hn
        simp [hcz]
    rw [hP_eval, Complex.re_sum, sum_Icc_neg_eq_zero_add_sum_fin]
    congr 1
    · simp [a₀]
    · refine Finset.sum_congr rfl fun m _ => ?_
      let θ : ℝ := (((m : ℕ) + 1 : ℝ) * ω₀) * s
      let n_pos : ℤ := (m : ℕ) + 1
      let n_neg : ℤ := -(((m : ℕ) + 1 : ℕ) : ℤ)
      have hpos_arg : 2 * ↑Real.pi * I * (n_pos : ℂ) * (s : ℂ) / (T : ℂ) =
          I * (θ : ℂ) := by
        dsimp only [θ, ω₀, n_pos]
        push_cast
        field_simp [hT_pos.ne']
      have hneg_arg : 2 * ↑Real.pi * I * (n_neg : ℂ) * (s : ℂ) / (T : ℂ) =
          -(I * (θ : ℂ)) := by
        dsimp only [θ, ω₀, n_neg]
        push_cast
        field_simp [hT_pos.ne']
      change (c n_pos * fourier (T := T) n_pos (s : AddCircle T)).re +
          (c n_neg * fourier (T := T) n_neg (s : AddCircle T)).re = _
      rw [fourier_coe_apply, fourier_coe_apply, hpos_arg, hneg_arg, re_mul_exp_neg_I_mul]
      dsimp only [a, n_pos, n_neg, θ]
      rw [← Complex.add_re, ← add_mul]
      congr 2
      push_cast
      rfl
  have hφ_eq (s : ℝ) :
      a₀ * Real.exp (-α * s) +
        ∑ m : Fin M, (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (s : ℂ))).re =
      Real.exp (-α * s) * (P_trig (s : AddCircle T)).re := by
    rw [htrig_re s, mul_add, mul_comm a₀ (Real.exp (-α * s)), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    have hexp_split : exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (s : ℂ)) =
        (Real.exp (-α * s) : ℂ) * exp (I * ((((m : ℕ) + 1 : ℝ) * ω₀) * (s : ℂ))) := by
      rw [add_mul, Complex.exp_add, ← Complex.ofReal_mul, Complex.ofReal_exp]
      congr 2
      push_cast
      ring
    rw [hexp_split, ← mul_assoc, mul_comm (a m) (Real.exp (-α * s) : ℂ), mul_assoc,
      Complex.re_ofReal_mul]
  have hrank : separableRank (fun x : Fin d → ℝ =>
      a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
        ∑ m : Fin M,
          (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (∑ j, x j ^ 2 : ℝ))).re) ≤
      (1 + d * M : ℕ) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    obtain ⟨i₀⟩ := ‹Nonempty (Fin d)›
    have h0_prod : IsSumOfProducts
        (fun x : Fin d → ℝ => a₀ * Real.exp (-α * ∑ j, x j ^ 2)) 1 := by
      refine ⟨fun _ j u => (if j = i₀ then a₀ else 1) * Real.exp (-α * u ^ 2), fun x => ?_⟩
      simp only [Fin.sum_univ_one]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then a₀ else (1 : ℝ)) = 1 :=
        Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
      simp [her]
    have hm_prod (m : Fin M) : IsSumOfProducts
        (fun x : Fin d → ℝ =>
          (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (∑ j, x j ^ 2 : ℝ))).re) d := by
      let rate : ℂ := (-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)
      have hcpx : IsSumOfProducts
          (fun x : Fin d → ℝ => a m * exp (rate * (∑ j, x j ^ 2 : ℝ))) 1 := by
        refine ⟨fun _ j u => (if j = i₀ then a m else 1) * exp (rate * (u ^ 2 : ℝ)), fun x => ?_⟩
        simp only [Fin.sum_univ_one]
        rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
        congr 1
        · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
          have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then a m else (1 : ℂ)) = 1 :=
            Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
          simp [her]
        · congr 1
          rw [← Finset.mul_sum]
          push_cast
          rfl
      have hre := hcpx.re (by omega)
      rw [one_mul] at hre
      exact hre
    have hsum_prod := IsSumOfProducts.finsetSum hm_prod
    have hcard : (∑ _ : Fin M, d) = d * M := by simp [mul_comm]
    rw [hcard] at hsum_prod
    exact iInf₂_le _ (h0_prod.add hsum_prod)
  refine ⟨ω₀, M, a₀, a, hω₀_pos, hrank, fun x => ?_⟩
  set s := ∑ j : Fin d, x j ^ 2
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
  rw [hφ_eq s, ← hψ₀_eq s hs0]
  have hexp_le1 : Real.exp (-α * s) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hexp_pos : 0 < Real.exp (-α * s) := Real.exp_pos _
  have htrig_err : |Real.exp (-α * s) * (P_trig (s : AddCircle T)).re -
      Real.exp (-α * s) * (G (s : AddCircle T)).re| < ε / 4 := by
    rw [← mul_sub, abs_mul, abs_of_pos hexp_pos]
    have hpt : |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re| < ε / 4 := by
      have h1 : |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re| ≤
          ‖P_trig (s : AddCircle T) - G (s : AddCircle T)‖ := by
        rw [← Complex.sub_re]
        exact Complex.abs_re_le_norm _
      have h2 : ‖P_trig (s : AddCircle T) - G (s : AddCircle T)‖ ≤ ‖P_trig - G‖ :=
        ContinuousMap.norm_coe_le_norm (P_trig - G) (s : AddCircle T)
      have h3 : ‖P_trig - G‖ < ε / 4 := by
        rwa [dist_comm, dist_eq_norm] at hGP_dist
      exact (h1.trans h2).trans_lt h3
    calc
      Real.exp (-α * s) * |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re|
          ≤ 1 * |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re| :=
        mul_le_mul_of_nonneg_right hexp_le1 (abs_nonneg _)
      _ < ε / 4 := by linarith
  have hG_err : |Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s| < 3 * (ε / 4) := by
    by_cases hsT : s < T - 1
    · have hs_Ico : s ∈ Set.Ico 0 T := ⟨hs0, by linarith⟩
      have hGs : (G (s : AddCircle T)).re = g_raw s := by
        have hcoe : G (s : AddCircle T) = (g_raw s : ℂ) := by
          simpa [G] using AddCircle.liftIco_zero_coe_apply (p := T)
            (f := fun v => (g_raw v : ℂ)) hs_Ico
        rw [hcoe, Complex.ofReal_re]
      rw [hGs]
      have hc2_z : c₂ s = 0 := by
        dsimp only [c₂]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hg_s : Real.exp (-α * s) * g_raw s = c₁ s * ψ₀ s := by
        dsimp only [g_raw]
        rw [hc2_z, zero_mul, add_zero, ← mul_assoc, mul_comm (Real.exp (-α * s)) (c₁ s),
          mul_assoc, ← mul_assoc (Real.exp (-α * s)), ← Real.exp_add]
        have : -α * s + α * s = 0 := by ring
        rw [this, Real.exp_zero, one_mul]
      rw [hg_s]
      by_cases hsS : s ≤ S₀
      · have hc1_1 : c₁ s = 1 := by
          dsimp only [c₁]
          rw [min_eq_left (by linarith), max_eq_right zero_le_one]
        rw [hc1_1, one_mul, sub_self, abs_zero]
        positivity
      · push Not at hsS
        have hc1_01 : 0 ≤ c₁ s ∧ c₁ s ≤ 1 := by
          dsimp only [c₁]
          exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
        have hsub : |c₁ s * ψ₀ s - ψ₀ s| ≤ |ψ₀ s| := by
          rw [show c₁ s * ψ₀ s - ψ₀ s = (c₁ s - 1) * ψ₀ s by ring, abs_mul]
          have : |c₁ s - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          calc
            |c₁ s - 1| * |ψ₀ s| ≤ 1 * |ψ₀ s| :=
              mul_le_mul_of_nonneg_right this (abs_nonneg _)
            _ = |ψ₀ s| := one_mul _
        exact (hsub.trans_lt (hψ_tail s hsS.le)).trans (by linarith)
    · push Not at hsT
      have hsS : S₀ ≤ s := by linarith
      have hsT1 : T₁ ≤ s := by
        have : T₁ + 1 ≤ T := le_max_left _ _
        linarith
      have hexp_tail : Real.exp (-α * s) * M_bound < ε / 4 := by
        have hd_lt := hT₁ s hsT1
        rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos hexp_pos hM_pos)] at hd_lt
        exact hd_lt
      have h1 : |Real.exp (-α * s) * (G (s : AddCircle T)).re| < ε / 4 := by
        rw [abs_mul, abs_of_pos hexp_pos]
        exact (mul_le_mul_of_nonneg_left (hG_bound _) hexp_pos.le).trans_lt hexp_tail
      have h2 : |ψ₀ s| < ε / 4 := hψ_tail s hsS
      have htri : |Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s| ≤
          |Real.exp (-α * s) * (G (s : AddCircle T)).re| + |ψ₀ s| := abs_sub _ _
      linarith
  have htri_tot : |Real.exp (-α * s) * (P_trig (s : AddCircle T)).re - ψ₀ s| ≤
      |Real.exp (-α * s) * (P_trig (s : AddCircle T)).re -
        Real.exp (-α * s) * (G (s : AddCircle T)).re| +
      |Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s| := by
    simpa using abs_add_le
      (Real.exp (-α * s) * (P_trig (s : AddCircle T)).re -
        Real.exp (-α * s) * (G (s : AddCircle T)).re)
      (Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s)
  linarith

end UniversalApproximation

end KernelRank
