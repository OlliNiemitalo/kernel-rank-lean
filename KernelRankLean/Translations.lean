import KernelRankLean.RowSpan

/-!
# Radial kernels, additive Hankel kernels, and the span of translates

In any dimension `d`, squaring each coordinate maps `ℝ` onto `[0, ∞)`, so the `d`-way separable
rank of the radial kernel `x ↦ φ (∑ i, x i ^ 2)` on `ℝ^d` equals that of the additive Hankel
kernel `s ↦ φ (∑ i, s i)` on `[0, ∞)^d`. Padding a 2-D input with zeros also bounds the 2-D
radial rank by the `d`-D radial rank whenever `d ≥ 2`.

In 2-D (`d = 2`), the rows of `(s₀, s₁) ↦ φ (s₀ + s₁)` are literally the translates
`u ↦ φ (u + t)` of `φ` on `[0, ∞)`, so the 2-D radial separable rank is the dimension of the
translate span.
-/

open NNReal

namespace KernelRank

/-- The span of the translates `u ↦ φ (u + t)`, `t ≥ 0`, of a profile, as functions on `[0, ∞)`. -/
def translateSpan {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) : Submodule 𝕜 (ℝ≥0 → 𝕜) :=
  Submodule.span 𝕜 (Set.range fun (t : ℝ≥0) (u : ℝ≥0) => φ (u + t))

/-- Squaring maps `ℝ` onto `[0, ∞)`, so the `d`-D radial kernel `x ↦ φ (∑ i, x i ^ 2)` has the
same separable rank as the `d`-D Hankel kernel `s ↦ φ (∑ i, s i)` on `[0, ∞)^d`. -/
theorem separableRank_radial_eq_hankel {𝕜 : Type*} [CommSemiring 𝕜] (d : ℕ) (φ : ℝ → 𝕜) :
    separableRank (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2)) =
      separableRank (fun s : Fin d → ℝ≥0 => φ (∑ i, (s i : ℝ))) := by
  let sqNN (x : ℝ) : ℝ≥0 := ⟨x ^ 2, sq_nonneg x⟩
  have hsurj : Function.Surjective sqNN := fun s =>
    ⟨Real.sqrt s, Subtype.ext (Real.sq_sqrt s.2)⟩
  exact separableRank_comp_surjective (X := fun _ : Fin d => ℝ≥0) (Y := fun _ : Fin d => ℝ)
    (fun s => φ (∑ i, (s i : ℝ))) (g := fun _ => sqNN) (fun _ => hsurj)

/-- Restricting a `d`-D radial kernel (`d ≥ 2`) to its first two coordinates bounds the 2-D
radial rank by the `d`-D radial rank. -/
theorem separableRank_radial_two_le {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → 𝕜) :
    separableRank (fun y : Fin 2 → ℝ => φ (∑ k, y k ^ 2)) ≤
      separableRank (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2)) := by
  have hpad : (fun y : Fin 2 → ℝ => φ (∑ i : Fin d, padTwo y i ^ 2)) =
      fun y : Fin 2 → ℝ => φ (∑ k : Fin 2, y k ^ 2) := by
    funext y
    congr 1
    have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin d => (i : ℕ) < 2) (fun i => padTwo y i ^ 2)).symm
    have hrest : ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ (i : ℕ) < 2),
        padTwo y i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hi' : ¬ (i : ℕ) < 2 := (Finset.mem_filter.mp hi).2
        simp [padTwo, hi']
    have htwo : ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2), padTwo y i ^ 2 =
        y 0 ^ 2 + y 1 ^ 2 := by
      have hset : Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2) =
          {Fin.castLE hd 0, Fin.castLE hd 1} := by
        ext ⟨i, hi⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE, Fin.val_zero, Fin.val_one]
        omega
      have hne : Fin.castLE hd 0 ≠ Fin.castLE hd 1 := by simp [Fin.ext_iff]
      rw [hset, Finset.sum_pair hne]
      simp [padTwo, Fin.castLE]
    rw [hsplit, hrest, add_zero, htwo, Fin.sum_univ_two]
  have h := separableRank_padTwo_le hd (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2))
  rwa [hpad] at h

/-- The row span of the 2-D Hankel kernel `(s₀, s₁) ↦ φ (s₀ + s₁)` is `translateSpan φ`. -/
lemma rowSpan_hankelTwo {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) :
    rowSpan (fun s : Fin 2 → ℝ≥0 => φ (∑ i, (s i : ℝ))) = translateSpan φ := by
  unfold rowSpan translateSpan
  apply congrArg (Submodule.span 𝕜)
  ext f
  simp [Fin.sum_univ_two]

/-- A 2-D radial kernel has finite separable rank iff the translates of its profile on `[0, ∞)`
span a finite-dimensional space. -/
theorem separableRank_radial_two_lt_top_iff {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) < ⊤ ↔
      FiniteDimensional 𝕜 (translateSpan φ) := by
  rw [separableRank_radial_eq_hankel, separableRank_lt_top_iff, rowSpan_hankelTwo]

/-- The separable rank of a 2-D radial kernel is the dimension of the span of its profile's
translates on `[0, ∞)`, when that is finite. -/
theorem separableRank_radial_two_eq_finrank {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜)
    [FiniteDimensional 𝕜 (translateSpan φ)] :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) =
      Module.finrank 𝕜 (translateSpan φ) := by
  have : FiniteDimensional 𝕜 (rowSpan (fun s : Fin 2 → ℝ≥0 => φ (∑ i, (s i : ℝ)))) := by
    rwa [rowSpan_hankelTwo]
  rw [separableRank_radial_eq_hankel, separableRank_eq_finrank_rowSpan, rowSpan_hankelTwo]

end KernelRank
