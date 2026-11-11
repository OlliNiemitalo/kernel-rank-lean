import KernelRankLean.Defs

/-!
# Two-variable separable rank as the dimension of the row span

For a two-coordinate kernel `K : (Fin 2 → α) → 𝕜`, the rows `x ↦ K ![x, y]` of a sum of `N`
products lie in the span of the `N` functions of the first coordinate, so the row span has
dimension at most `N`. Conversely, expanding each row in a basis of a finite-dimensional row span
writes `K` as a sum of `finrank` products. So in two coordinates, the separable rank is the
dimension of the row span when that is finite, and `⊤` otherwise.
-/

namespace KernelRank

variable {𝕜 α : Type*}

/-- Pairs `(x, y)` as two-coordinate vectors `Fin 2 → α`. -/
def fin2Vec (x y : α) : Fin 2 → α
  | 0 => x
  | 1 => y

@[simp] lemma fin2Vec_zero (x y : α) : fin2Vec x y 0 = x := rfl

@[simp] lemma fin2Vec_one (x y : α) : fin2Vec x y 1 = y := rfl

lemma fin2Vec_eta (z : Fin 2 → α) : fin2Vec (z 0) (z 1) = z := by
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl

variable [Field 𝕜]

/-- The span of the rows `x ↦ K (fin2Vec x y)` of a two-coordinate kernel. -/
def rowSpan (K : (Fin 2 → α) → 𝕜) : Submodule 𝕜 (α → 𝕜) :=
  Submodule.span 𝕜 (Set.range fun (y : α) (x : α) => K (fin2Vec x y))

lemma row_mem_rowSpan (K : (Fin 2 → α) → 𝕜) (y : α) :
    (fun x => K (fin2Vec x y)) ∈ rowSpan K :=
  Submodule.subset_span ⟨y, rfl⟩

/-- A sum of `N` products has a row span inside the span of its `N` functions of coordinate `0`. -/
lemma rowSpan_le_of_isSumOfProducts {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    {f : Fin N → Fin 2 → α → 𝕜}
    (hK : ∀ z, K z = ∑ n, ∏ i : Fin 2, f n i (z i)) :
    rowSpan K ≤ Submodule.span 𝕜 (Set.range fun n => f n 0) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨y, rfl⟩
  have : (fun x => K (fin2Vec x y)) = ∑ n, f n 1 y • f n 0 := by
    funext x
    simp [hK, Fin.prod_univ_two, Finset.sum_apply, mul_comm]
  change (fun x => K (fin2Vec x y)) ∈ Submodule.span 𝕜 (Set.range fun n => f n 0)
  rw [this]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

lemma finiteDimensional_rowSpan_of_isSumOfProducts {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : FiniteDimensional 𝕜 (rowSpan K) := by
  obtain ⟨f, hK⟩ := hK
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range fun n => f n 0)
  exact Submodule.finiteDimensional_of_le (rowSpan_le_of_isSumOfProducts hK)

lemma finrank_rowSpan_le_of_isSumOfProducts {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : Module.finrank 𝕜 (rowSpan K) ≤ N := by
  obtain ⟨f, hK⟩ := hK
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range fun n => f n 0)
  calc Module.finrank 𝕜 (rowSpan K)
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun n => f n 0)) :=
        Submodule.finrank_mono (rowSpan_le_of_isSumOfProducts hK)
    _ ≤ Fintype.card (Fin N) := finrank_range_le_card fun n => f n 0
    _ = N := Fintype.card_fin N

/-- A finite-dimensional row span gives a sum of `finrank` products: expand each row in a basis. -/
lemma isSumOfProducts_finrank_rowSpan (K : (Fin 2 → α) → 𝕜)
    [FiniteDimensional 𝕜 (rowSpan K)] :
    IsSumOfProducts K (Module.finrank 𝕜 (rowSpan K)) := by
  let b := Module.finBasis 𝕜 (rowSpan K)
  refine ⟨fun i => fin2Vec (b i : α → 𝕜) (fun y => b.repr ⟨_, row_mem_rowSpan K y⟩ i), fun z => ?_⟩
  have := congrArg (fun w : rowSpan K => (w : α → 𝕜) (z 0))
    (b.sum_repr ⟨_, row_mem_rowSpan K (z 1)⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at this
  conv_lhs => rw [← fin2Vec_eta z]
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_two]
  exact mul_comm _ _

/-- In two coordinates, the separable rank is finite iff the row span is finite-dimensional. -/
theorem separableRank_lt_top_iff (K : (Fin 2 → α) → 𝕜) :
    separableRank K < ⊤ ↔ FiniteDimensional 𝕜 (rowSpan K) := by
  constructor
  · intro hlt
    by_contra hfin
    refine hlt.ne (iInf₂_eq_top.mpr fun N hN => ?_)
    exact absurd (finiteDimensional_rowSpan_of_isSumOfProducts hN) hfin
  · intro hfin
    exact lt_of_le_of_lt (iInf₂_le _ (isSumOfProducts_finrank_rowSpan K)) (by simp)

/-- With a finite-dimensional row span, the two-coordinate separable rank is its dimension. -/
theorem separableRank_eq_finrank_rowSpan (K : (Fin 2 → α) → 𝕜)
    [FiniteDimensional 𝕜 (rowSpan K)] :
    separableRank K = Module.finrank 𝕜 (rowSpan K) := by
  refine le_antisymm (iInf₂_le _ (isSumOfProducts_finrank_rowSpan K)) ?_
  exact le_iInf₂ fun N hN => by exact_mod_cast finrank_rowSpan_le_of_isSumOfProducts hN

end KernelRank
