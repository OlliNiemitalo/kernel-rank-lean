import KernelRankLean.RowSpan

/-!
# Radial rows are translates of the profile

The row `x ↦ φ (x ^ 2 + y ^ 2)` of a radial kernel is the translate `u ↦ φ (u + t)` with
`t = y ^ 2`, read at `u = x ^ 2`. Reading at `x ^ 2` is injective on functions on `[0, ∞)`, and
`y ^ 2` takes every value `t ≥ 0`. So the row span is a copy of the span of the translates of `φ`
on `[0, ∞)`, and the separable rank is that span's dimension.
-/

open NNReal

namespace KernelRank

/-- The span of the translates `u ↦ φ (u + t)`, `t ≥ 0`, of a profile, as functions on `[0, ∞)`. -/
def translateSpan (φ : ℝ → ℝ) : Submodule ℝ (ℝ≥0 → ℝ) :=
  Submodule.span ℝ (Set.range fun (t : ℝ≥0) (u : ℝ≥0) => φ (u + t))

/-- Reading a function on `[0, ∞)` at `x ^ 2`. -/
def atSquare : (ℝ≥0 → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun g x := g ⟨x ^ 2, sq_nonneg x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma atSquare_injective : Function.Injective atSquare := by
  intro g g' h
  funext u
  have hu : (⟨Real.sqrt u ^ 2, sq_nonneg _⟩ : ℝ≥0) = u := Subtype.ext (Real.sq_sqrt u.2)
  have := congrFun h (Real.sqrt u)
  simp only [atSquare, LinearMap.coe_mk, AddHom.coe_mk, hu] at this
  exact this

/-- The radial kernel's row span is the translate span read at `x ^ 2`. -/
lemma rowSpan_radial (φ : ℝ → ℝ) :
    rowSpan (fun x y => φ (x ^ 2 + y ^ 2)) = (translateSpan φ).map atSquare := by
  rw [translateSpan, Submodule.map_span, rowSpan]
  congr 1
  ext f
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨⟨y ^ 2, sq_nonneg y⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨Real.sqrt t, ?_⟩
    funext x
    simp only [atSquare, LinearMap.coe_mk, AddHom.coe_mk, Real.sq_sqrt (NNReal.coe_nonneg t)]
    rfl

/-- The translate span and the radial kernel's row span are isomorphic. -/
noncomputable def translateSpanEquivRowSpan (φ : ℝ → ℝ) :
    translateSpan φ ≃ₗ[ℝ] rowSpan (fun x y => φ (x ^ 2 + y ^ 2)) :=
  (Submodule.equivMapOfInjective atSquare atSquare_injective _).trans
    (LinearEquiv.ofEq _ _ (rowSpan_radial φ).symm)

/-- A radial kernel has finite separable rank exactly when the translates of its profile on
`[0, ∞)` span a finite-dimensional space. -/
theorem separableRank_radial_lt_top_iff (φ : ℝ → ℝ) :
    separableRank (fun x y => φ (x ^ 2 + y ^ 2)) < ⊤ ↔ FiniteDimensional ℝ (translateSpan φ) := by
  rw [separableRank_lt_top_iff]
  exact ⟨fun _ => (translateSpanEquivRowSpan φ).symm.finiteDimensional,
    fun _ => (translateSpanEquivRowSpan φ).finiteDimensional⟩

/-- The separable rank of a radial kernel is the dimension of the span of its profile's
translates on `[0, ∞)`, when that is finite. -/
theorem separableRank_radial_eq_finrank (φ : ℝ → ℝ) [FiniteDimensional ℝ (translateSpan φ)] :
    separableRank (fun x y => φ (x ^ 2 + y ^ 2)) = Module.finrank ℝ (translateSpan φ) := by
  have := (translateSpanEquivRowSpan φ).finiteDimensional
  rw [separableRank_eq_finrank_rowSpan, (translateSpanEquivRowSpan φ).finrank_eq]

end KernelRank
