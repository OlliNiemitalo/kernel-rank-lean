import KernelRankLean.Defs

/-!
# Separable rank as the dimension of the row span

The rows `x ↦ K x y` of a sum of `N` products lie in the span of the `N` functions of `x`, so the
row span has dimension at most `N`. Conversely, expanding each row in a basis of a
finite-dimensional row span writes `K` as a sum of `finrank` products. So the separable rank is
the dimension of the row span when that is finite, and `⊤` otherwise.
-/

namespace KernelRank

variable {𝕜 X Y : Type*} [Field 𝕜]

/-- The span of the rows `x ↦ K x y` of a kernel, as functions of `x`. -/
def rowSpan (K : X → Y → 𝕜) : Submodule 𝕜 (X → 𝕜) :=
  Submodule.span 𝕜 (Set.range fun y x => K x y)

lemma row_mem_rowSpan (K : X → Y → 𝕜) (y : Y) : (fun x => K x y) ∈ rowSpan K :=
  Submodule.subset_span ⟨y, rfl⟩

/-- A sum of `N` products has a row span inside the span of its `N` functions of `x`. -/
lemma rowSpan_le_of_isSumOfProducts {K : X → Y → 𝕜} {N : ℕ}
    {h : Fin N → X → 𝕜} {v : Fin N → Y → 𝕜}
    (hK : ∀ x y, K x y = ∑ n, h n x * v n y) :
    rowSpan K ≤ Submodule.span 𝕜 (Set.range h) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨y, rfl⟩
  have : (fun x => K x y) = ∑ n, v n y • h n := by
    funext x
    simp [hK, Finset.sum_apply, mul_comm]
  change (fun x => K x y) ∈ Submodule.span 𝕜 (Set.range h)
  rw [this]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

lemma finiteDimensional_rowSpan_of_isSumOfProducts {K : X → Y → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : FiniteDimensional 𝕜 (rowSpan K) := by
  obtain ⟨h, v, hK⟩ := hK
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range h)
  exact Submodule.finiteDimensional_of_le (rowSpan_le_of_isSumOfProducts hK)

lemma finrank_rowSpan_le_of_isSumOfProducts {K : X → Y → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : Module.finrank 𝕜 (rowSpan K) ≤ N := by
  obtain ⟨h, v, hK⟩ := hK
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range h)
  calc Module.finrank 𝕜 (rowSpan K)
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range h)) :=
        Submodule.finrank_mono (rowSpan_le_of_isSumOfProducts hK)
    _ ≤ Fintype.card (Fin N) := finrank_range_le_card h
    _ = N := Fintype.card_fin N

/-- A finite-dimensional row span gives a sum of `finrank` products: expand each row in a basis. -/
lemma isSumOfProducts_finrank_rowSpan (K : X → Y → 𝕜) [FiniteDimensional 𝕜 (rowSpan K)] :
    IsSumOfProducts K (Module.finrank 𝕜 (rowSpan K)) := by
  let b := Module.finBasis 𝕜 (rowSpan K)
  refine ⟨fun i => (b i : X → 𝕜), fun i y => b.repr ⟨_, row_mem_rowSpan K y⟩ i, fun x y => ?_⟩
  have := congrArg (fun w : rowSpan K => (w : X → 𝕜) x) (b.sum_repr ⟨_, row_mem_rowSpan K y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The separable rank is finite exactly when the row span is finite-dimensional. -/
theorem separableRank_lt_top_iff (K : X → Y → 𝕜) :
    separableRank K < ⊤ ↔ FiniteDimensional 𝕜 (rowSpan K) := by
  constructor
  · intro hlt
    by_contra hfin
    refine hlt.ne (iInf₂_eq_top.mpr fun N hN => ?_)
    exact absurd (finiteDimensional_rowSpan_of_isSumOfProducts hN) hfin
  · intro hfin
    exact lt_of_le_of_lt (iInf₂_le _ (isSumOfProducts_finrank_rowSpan K)) (by simp)

/-- With a finite-dimensional row span, the separable rank is its dimension. -/
theorem separableRank_eq_finrank_rowSpan (K : X → Y → 𝕜) [FiniteDimensional 𝕜 (rowSpan K)] :
    separableRank K = Module.finrank 𝕜 (rowSpan K) := by
  refine le_antisymm (iInf₂_le _ (isSumOfProducts_finrank_rowSpan K)) ?_
  exact le_iInf₂ fun N hN => by exact_mod_cast finrank_rowSpan_le_of_isSumOfProducts hN

end KernelRank
