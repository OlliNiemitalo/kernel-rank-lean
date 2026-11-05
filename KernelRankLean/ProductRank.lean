import Mathlib

/-!
# The span of a sum of products with independent coefficients

If `G t = ∑ j, a j t • f j` and the coefficient functions `a j` are linearly independent, then the
coefficient vectors `(a j t)_j` span all of `ι → ℝ` (a functional vanishing on all of them would be
a linear relation between the `a j`). So the `G t` span the same space as the `f j`, and when the
`f j` are linearly independent too, that space has dimension `card ι`.
-/

namespace KernelRank

variable {ι V T : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- Linearly independent coefficient functions have coefficient vectors spanning `ι → ℝ`. -/
lemma span_coefficientVectors_eq_top {a : ι → T → ℝ} (ha : LinearIndependent ℝ a) :
    Submodule.span ℝ (Set.range fun t j => a j t) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set c : ι → ℝ := fun i => φ (fun j => if i = j then 1 else 0)
  have hφc : ∀ x : ι → ℝ, φ x = ∑ i, x i * c i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x]
    rfl
  have hrel : ∑ i, c i • a i = 0 := by
    funext t
    have : φ (fun j => a j t) = 0 := hle (Submodule.subset_span ⟨t, rfl⟩)
    rw [hφc] at this
    simpa [Finset.sum_apply, mul_comm] using this
  have hc : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp ha c hrel
  exact hφ (LinearMap.ext fun x => by simp [hφc, hc])

/-- If `G t = ∑ j, a j t • f j` with linearly independent `a j`, the `G t` span the span of the
`f j`. -/
theorem span_range_eq_of_linearIndependent_coefficients (f : ι → V) {a : ι → T → ℝ}
    (ha : LinearIndependent ℝ a) {G : T → V} (hG : ∀ t, G t = ∑ j, a j t • f j) :
    Submodule.span ℝ (Set.range G) = Submodule.span ℝ (Set.range f) := by
  let L := Fintype.linearCombination ℝ f
  have hGL : G = L ∘ fun t j => a j t := by
    funext t
    simp [L, hG, Fintype.linearCombination_apply]
  rw [hGL, Set.range_comp, ← Submodule.map_span, span_coefficientVectors_eq_top ha,
    Submodule.map_top, Fintype.range_linearCombination]

/-- If moreover the `f j` are linearly independent, the `G t` span a space of dimension `card ι`. -/
theorem finrank_span_range_eq_card {f : ι → V} (hf : LinearIndependent ℝ f) {a : ι → T → ℝ}
    (ha : LinearIndependent ℝ a) {G : T → V} (hG : ∀ t, G t = ∑ j, a j t • f j) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range G)) = Fintype.card ι := by
  rw [span_range_eq_of_linearIndependent_coefficients f ha hG, finrank_span_eq_card hf]

end KernelRank
