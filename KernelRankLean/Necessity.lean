import KernelRankLean.Translations
import KernelRankLean.Semigroup
import KernelRankLean.Representation

/-!
# Necessity: a finite-rank radial kernel has a profile made of components

Let the translates `u ↦ φ (u + t)` of a profile `φ`, continuous on `[0, ∞)`, span a
finite-dimensional space `W` of functions on `[0, ∞)`.

* Translation by `t` maps `W` to itself; in a basis of `W` it is a matrix `M t`, with
  `M (s + t) = M s * M t` and `M 0 = 1`.
* The functions in `W` are continuous, and finitely many evaluations determine them, so the
  coordinates, and `M`, depend continuously on `t`. Hence `M t = exp (t A)`.
* `φ t` is a fixed linear functional of `M t` applied to a fixed vector. Splitting the vector into
  generalized eigenvectors of `A`, each piece contributes `exp (μ t)` times a polynomial in `t`.
* Conjugate pairing then regroups the sum into components.
-/

open Complex Polynomial NNReal Matrix

namespace KernelRank

/-! ### Translation on the span of the translates -/

/-- Translation of a function on `[0, ∞)` by `t`. -/
noncomputable def shift (t : ℝ≥0) : (ℝ≥0 → ℝ) →ₗ[ℝ] (ℝ≥0 → ℝ) :=
  LinearMap.funLeft ℝ ℝ (· + t)

lemma shift_apply (t : ℝ≥0) (g : ℝ≥0 → ℝ) (u : ℝ≥0) : shift t g u = g (u + t) := rfl

variable (φ : ℝ → ℝ)

lemma translate_mem_translateSpan (s : ℝ≥0) :
    (fun u : ℝ≥0 => φ (u + s)) ∈ translateSpan φ :=
  Submodule.subset_span ⟨s, rfl⟩

lemma shift_mem_translateSpan (t : ℝ≥0) {g : ℝ≥0 → ℝ} (hg : g ∈ translateSpan φ) :
    shift t g ∈ translateSpan φ := by
  have : translateSpan φ ≤ (translateSpan φ).comap (shift t) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, rfl⟩
    refine Submodule.subset_span ⟨s + t, funext fun u => ?_⟩
    simp only [shift_apply, NNReal.coe_add]
    ring_nf
  exact this hg

/-- Translation restricted to the span of the translates. -/
noncomputable def shiftW (t : ℝ≥0) : translateSpan φ →ₗ[ℝ] translateSpan φ :=
  (shift t).restrict fun _ hg => shift_mem_translateSpan φ t hg

lemma shiftW_apply (t : ℝ≥0) (g : translateSpan φ) (u : ℝ≥0) :
    (shiftW φ t g : ℝ≥0 → ℝ) u = (g : ℝ≥0 → ℝ) (u + t) := rfl

lemma shiftW_zero : shiftW φ 0 = 1 := by
  ext g u
  simp [shiftW_apply]

lemma shiftW_add (s t : ℝ≥0) : shiftW φ (s + t) = shiftW φ s * shiftW φ t := by
  ext g u
  simp only [shiftW_apply, Module.End.mul_apply, add_assoc]

/-- The functions in the span of the translates are continuous. -/
lemma continuous_of_mem_translateSpan {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ici 0))
    {g : ℝ≥0 → ℝ} (hg : g ∈ translateSpan φ) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact hφ.comp_continuous (NNReal.continuous_coe.add continuous_const)
      fun u => Set.mem_Ici.mpr (add_nonneg u.2 s.2)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

/-- Evaluation of the functions in the span at a finite set of points. -/
noncomputable def evalAt (F : Finset ℝ≥0) : translateSpan φ →ₗ[ℝ] (F → ℝ) :=
  LinearMap.pi fun u : F => (LinearMap.proj (u : ℝ≥0)).comp (translateSpan φ).subtype

lemma mem_ker_evalAt {F : Finset ℝ≥0} {g : translateSpan φ} :
    g ∈ LinearMap.ker (evalAt φ F) ↔ ∀ u ∈ F, (g : ℝ≥0 → ℝ) u = 0 := by
  simp [evalAt, funext_iff]

/-- Finitely many points determine the functions in a finite-dimensional span. -/
lemma exists_evalAt_injective [FiniteDimensional ℝ (translateSpan φ)] :
    ∃ F : Finset ℝ≥0, LinearMap.ker (evalAt φ F) = ⊥ := by
  classical
  obtain ⟨F, -, hF⟩ := (measure fun F : Finset ℝ≥0 =>
    Module.finrank ℝ (LinearMap.ker (evalAt φ F))).wf.has_min Set.univ ⟨∅, Set.mem_univ _⟩
  refine ⟨F, (Submodule.eq_bot_iff _).mpr fun g hg => ?_⟩
  by_contra hne
  obtain ⟨u, hu⟩ : ∃ u, (g : ℝ≥0 → ℝ) u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Subtype.ext (funext hall))
  have hlt : LinearMap.ker (evalAt φ (insert u F)) < LinearMap.ker (evalAt φ F) := by
    refine lt_of_le_of_ne (fun h hh => ?_) fun heq => ?_
    · rw [mem_ker_evalAt] at hh ⊢
      exact fun v hv => hh v (Finset.mem_insert_of_mem hv)
    · have : g ∈ LinearMap.ker (evalAt φ (insert u F)) := heq ▸ hg
      rw [mem_ker_evalAt] at this
      exact hu (this u (Finset.mem_insert_self u F))
  exact hF (insert u F) (Set.mem_univ _) (Submodule.finrank_lt_finrank_of_lt hlt)

/-! ### The matrix semigroup -/

section Matrix

variable [FiniteDimensional ℝ (translateSpan φ)]

/-- A basis of the span of the translates. -/
noncomputable abbrev basisW := Module.finBasis ℝ (translateSpan φ)

/-- The matrix of translation by `t ≥ 0`, as a complex matrix. -/
noncomputable def shiftMatrix (t : ℝ) :
    Matrix (Fin (Module.finrank ℝ (translateSpan φ))) (Fin (Module.finrank ℝ (translateSpan φ))) ℂ :=
  (LinearMap.toMatrix (basisW φ) (basisW φ) (shiftW φ t.toNNReal)).map Complex.ofRealHom

lemma shiftMatrix_zero : shiftMatrix φ 0 = 1 := by
  simp [shiftMatrix, shiftW_zero, LinearMap.toMatrix_one, Matrix.map_one]

lemma shiftMatrix_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    shiftMatrix φ (s + t) = shiftMatrix φ s * shiftMatrix φ t := by
  rw [shiftMatrix, Real.toNNReal_add hs ht, shiftW_add, LinearMap.toMatrix_mul,
    Matrix.map_mul]
  rfl

/-- The coordinates of a translate depend continuously on the translation. -/
lemma continuous_repr_shiftW (hφ : ContinuousOn φ (Set.Ici 0)) (g : translateSpan φ) (i) :
    Continuous fun t : ℝ => (basisW φ).repr (shiftW φ t.toNNReal g) i := by
  obtain ⟨F, hF⟩ := exists_evalAt_injective φ
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (evalAt φ F) hF
  have hrepr : ∀ h : translateSpan φ,
      (basisW φ).repr h i = ((basisW φ).coord i ∘ₗ L) (evalAt φ F h) := by
    intro h
    have := LinearMap.congr_fun hL h
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [this]
  simp only [hrepr]
  refine (LinearMap.continuous_of_finiteDimensional _).comp (continuous_pi fun u => ?_)
  simp only [evalAt, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.proj_apply, shiftW_apply]
  exact (continuous_of_mem_translateSpan hφ g.2).comp (continuous_const.add continuous_real_toNNReal)

lemma continuous_shiftMatrix (hφ : ContinuousOn φ (Set.Ici 0)) : Continuous (shiftMatrix φ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [shiftMatrix, Matrix.map_apply, LinearMap.toMatrix_apply, Complex.ofRealHom_eq_coe]
  exact Complex.continuous_ofReal.comp (continuous_repr_shiftW φ hφ _ _)

/-- The profile read off the translation matrices: `φ t = ∑ i, (M t x₀) i * β i`. -/
lemma ofReal_eq_shiftMatrix_mulVec {t : ℝ} (ht : 0 ≤ t) :
    (φ t : ℂ) = ∑ i, (shiftMatrix φ t *ᵥ fun j =>
        ((basisW φ).repr ⟨_, translate_mem_translateSpan φ 0⟩ j : ℂ)) i *
      ((basisW φ i : ℝ≥0 → ℝ) 0 : ℂ) := by
  set g₀ : translateSpan φ := ⟨_, translate_mem_translateSpan φ 0⟩
  have hφt : φ t = (shiftW φ t.toNNReal g₀ : ℝ≥0 → ℝ) 0 := by
    simp [shiftW_apply, g₀, Real.coe_toNNReal t ht]
  have hcoord : ∀ i, (shiftMatrix φ t *ᵥ fun j => ((basisW φ).repr g₀ j : ℂ)) i =
      ((basisW φ).repr (shiftW φ t.toNNReal g₀) i : ℂ) := by
    intro i
    rw [← LinearMap.toMatrix_mulVec_repr (basisW φ) (basisW φ)]
    simp only [shiftMatrix]
    rw [show (fun j => ((basisW φ).repr g₀ j : ℂ)) = Complex.ofRealHom ∘ ⇑((basisW φ).repr g₀)
      from rfl, ← RingHom.map_mulVec]
    rfl
  simp only [hcoord]
  have hsum := congrArg (fun w : translateSpan φ => ((w : ℝ≥0 → ℝ) 0 : ℂ))
    ((basisW φ).sum_repr (shiftW φ t.toNNReal g₀))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul] at hsum
  rw [hφt, ← hsum]

end Matrix

/-! ### Exponentials on generalized eigenvectors -/

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- On a generalized eigenvector with eigenvalue `μ`, `exp (t A)` acts as `exp (μ t)` times a
polynomial in `t`. -/
lemma exp_smul_mulVec_of_genEigen (A : Matrix n n ℂ) (μ : ℂ) {v : n → ℂ} {k : ℕ}
    (hv : ((Matrix.toLin' A - μ • 1) ^ k) v = 0) (t : ℂ) :
    NormedSpace.exp (t • A) *ᵥ v = ∑ m ∈ Finset.range k,
      (Complex.exp (μ * t) * ((m.factorial : ℂ)⁻¹ * t ^ m)) • ((A - μ • 1) ^ m *ᵥ v) := by
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  set N := A - μ • (1 : Matrix n n ℂ) with hNdef
  have hN : ∀ m, N ^ m *ᵥ v = ((Matrix.toLin' A - μ • 1) ^ m) v := by
    intro m
    rw [← Matrix.toLin'_apply, Matrix.toLin'_pow]
    congr 2
    simp [N, Matrix.toLin'_one, Module.End.one_eq_id]
  have hsplit : t • A = algebraMap ℂ (Matrix n n ℂ) (μ * t) + t • N := by
    simp only [N, Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]
    rw [mul_comm t μ]
    abel
  have hcomm : Commute (algebraMap ℂ (Matrix n n ℂ) (μ * t)) (t • N) := Algebra.commutes _ _
  -- The exponential series of the nilpotent part stops after `k` terms.
  have hseries := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • N)).map
    (Matrix.mulVec.addMonoidHomLeft v) (continuous_id.matrix_mulVec continuous_const)
  have hterm : ∀ m, Matrix.mulVec.addMonoidHomLeft v ((m.factorial⁻¹ : ℂ) • (t • N) ^ m) =
      ((m.factorial : ℂ)⁻¹ * t ^ m) • (N ^ m *ᵥ v) := by
    intro m
    simp only [Matrix.mulVec.addMonoidHomLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, _root_.smul_pow,
      smul_smul, Matrix.smul_mulVec]
  have hfin : HasSum (fun m => Matrix.mulVec.addMonoidHomLeft v
      ((m.factorial⁻¹ : ℂ) • (t • N) ^ m))
      (∑ m ∈ Finset.range k, ((m.factorial : ℂ)⁻¹ * t ^ m) • (N ^ m *ᵥ v)) := by
    simp only [hterm]
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    rw [Finset.mem_range, not_lt] at hm
    have hzero : ((Matrix.toLin' A - μ • 1) ^ m) v = 0 := by
      rw [← Nat.sub_add_cancel hm, pow_add, Module.End.mul_apply, hv, map_zero]
    rw [hN, hzero, smul_zero]
  have hexpN := hseries.unique hfin
  have hadd : NormedSpace.exp (algebraMap ℂ (Matrix n n ℂ) (μ * t) + t • N) =
      NormedSpace.exp (algebraMap ℂ (Matrix n n ℂ) (μ * t)) * NormedSpace.exp (t • N) :=
    NormedSpace.exp_add_of_commute hcomm
  have halg : NormedSpace.exp (algebraMap ℂ (Matrix n n ℂ) (μ * t)) =
      algebraMap ℂ (Matrix n n ℂ) (NormedSpace.exp (μ * t)) :=
    (NormedSpace.algebraMap_exp_comm _).symm
  rw [hsplit, hadd, halg, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mulVec, Matrix.one_mulVec, ← Complex.exp_eq_exp_ℂ]
  change Complex.exp (μ * t) • Matrix.mulVec.addMonoidHomLeft v (NormedSpace.exp (t • N)) = _
  refine (congrArg (Complex.exp (μ * t) • ·) hexpN).trans ?_
  rw [Finset.smul_sum]
  simp only [smul_smul]

/-- **Necessity.** A profile, continuous on `[0, ∞)`, whose translates span a finite-dimensional
space is, on `[0, ∞)`, the profile of a representation. -/
theorem exists_representation_of_finiteDimensional (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0))
    [FiniteDimensional ℝ (translateSpan φ)] :
    ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s := by
  classical
  -- Translation is `exp (t A)` in the basis.
  obtain ⟨A, hA⟩ := exists_eq_exp_of_semigroup (shiftMatrix φ)
    (continuous_shiftMatrix φ hφ).continuousOn (shiftMatrix_zero φ)
    fun s t hs ht => shiftMatrix_add φ hs ht
  set x₀ : Fin (Module.finrank ℝ (translateSpan φ)) → ℂ := fun j =>
    ((basisW φ).repr ⟨_, translate_mem_translateSpan φ 0⟩ j : ℂ) with hx₀
  -- Split the starting vector into generalized eigenvectors.
  have hx : x₀ ∈ ⨆ μ, Module.End.maxGenEigenspace (Matrix.toLin' A) μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    trivial
  obtain ⟨f, hf, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  choose k hk using fun μ => (Module.End.mem_maxGenEigenspace _ _ _).mp (hf μ)
  let c : ℂ → ℕ → ℂ := fun μ m =>
    ∑ i, ((A - μ • 1) ^ m *ᵥ f μ) i * ((basisW φ i : ℝ≥0 → ℝ) 0 : ℂ)
  let Q : ℂ → ℂ[X] := fun μ =>
    ∑ m ∈ Finset.range (k μ), C ((m.factorial : ℂ)⁻¹ * c μ m) * X ^ m
  refine exists_representation_of_sum_expPoly φ f.support Q fun t ht => ?_
  have hsmul : t • A = (t : ℂ) • A := by
    ext i j
    simp [Complex.real_smul]
  rw [ofReal_eq_shiftMatrix_mulVec φ ht, hA t ht, ← hx₀, ← hfsum, Finsupp.sum,
    Matrix.mulVec_sum]
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hsmul]
  erw [exp_smul_mulVec_of_genEigen A μ (hk μ)]
  simp only [Q, c, expPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end Exp

end KernelRank
