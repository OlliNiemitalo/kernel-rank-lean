import KernelRankLean.Sufficiency
import KernelRankLean.Necessity

/-!
# Main theorems

A circularly symmetric kernel `K x y = φ (x ^ 2 + y ^ 2)`, with `φ` continuous on `[0, ∞)`,
splits into `N` products of one-variable functions, and no fewer, exactly when its profile
`φ` is, on `[0, ∞)`, a sum of components with distinct rates that together cost `N`
rendering terms.

So no other choice of 1-D filters renders a circularly symmetric kernel with fewer passes than
the components do, and every finite-rank circularly symmetric kernel is a sum of components.
-/

namespace KernelRank

/-- A radial kernel only depends on its profile on `[0, ∞)`. -/
lemma radial_congr {φ ψ : ℝ → ℝ} (h : ∀ s, 0 ≤ s → φ s = ψ s) :
    (fun x y : ℝ => φ (x ^ 2 + y ^ 2)) = fun x y => ψ (x ^ 2 + y ^ 2) :=
  funext fun x => funext fun y => h _ (by positivity)

/-- **Classification.** A radial kernel, with profile continuous on `[0, ∞)`, has finite
separable rank exactly when its profile is, on `[0, ∞)`, a sum of components. -/
theorem separableRank_radial_lt_top_iff_exists (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) :
    separableRank (fun x y => φ (x ^ 2 + y ^ 2)) < ⊤ ↔
      ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s := by
  constructor
  · intro h
    have := (separableRank_radial_lt_top_iff φ).mp h
    exact exists_representation_of_finiteDimensional φ hφ
  · rintro ⟨cs, hcs, hφcs⟩
    rw [radial_congr hφcs, separableRank_radial_profile hcs]
    simp

/-- **The separable rank of a radial kernel.** A radial kernel, with profile continuous on
`[0, ∞)`, has separable rank `N` exactly when its profile is, on `[0, ∞)`, a sum of components
with distinct rates costing `N` rendering terms in total. -/
theorem separableRank_radial_eq_iff (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x y => φ (x ^ 2 + y ^ 2)) = N ↔
      ∃ cs : List Component, IsRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ totalCost cs = N := by
  constructor
  · intro h
    obtain ⟨cs, hcs, hφcs⟩ :=
      (separableRank_radial_lt_top_iff_exists φ hφ).mp (by rw [h]; simp)
    refine ⟨cs, hcs, hφcs, ?_⟩
    rw [radial_congr hφcs, separableRank_radial_profile hcs] at h
    exact_mod_cast h
  · rintro ⟨cs, hcs, hφcs, rfl⟩
    rw [radial_congr hφcs, separableRank_radial_profile hcs]

end KernelRank
