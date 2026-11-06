import Experiments.NonstandardSemigroup

/-!
# Draft: the semigroup theorem in nonstandard language

This draft proves `M t = exp (t A)` the way a nonstandard analyst would write it, using a small
interface for nonstandard analysis. **Every `sorry` in this file is in that interface**, the
`Infrastructure` section below. Those are the general facts a Mathlib library for nonstandard
analysis would provide; nothing in them is specific to semigroups. The proof of
`exists_eq_exp_of_semigroup` itself has no `sorry`.

The interface models hyperreals as Mathlib does: `Hyp α` is the ultrapower of `α` along
`hyperfilter ℕ`, the natural extension `*f` of `f` is `ext f`, and `x ≈ₕ y` means that `x - y`
is infinitesimal. Mathlib has no transfer principle; the draft needs only one-variable instances
of it (`transfer_mem`, `transfer_le`, `transfer_eq`).

For a proof of the same theorem with no `sorry`, see `NonstandardSemigroup.lean`, which works
with sequences along the ultrafilter instead.
-/

open Filter NormedSpace Set
open scoped Topology

noncomputable section

namespace Experiments.NSA

/-! ## Infrastructure -/

/-- The ultrapower `*α` of `α`: germs of sequences along `hyperfilter ℕ`. -/
abbrev Hyp (α : Type*) : Type _ := Germ (hyperfilter ℕ : Filter ℕ) α

/-- The standard copy of `x` in `*α`. -/
abbrev std {α : Type*} (x : α) : Hyp α := Germ.const x

/-- The natural extension `*f` of `f`. -/
abbrev ext {α β : Type*} (f : α → β) (ξ : Hyp α) : Hyp β := Germ.map f ξ

/-- An unlimited hypernatural number. -/
def ω : Hyp ℕ := Germ.ofFun id

/-- Internal membership `ξ ∈ *s`. -/
def IMem {α : Type*} (ξ : Hyp α) (s : Set α) : Prop := ξ.LiftPred (· ∈ s)

/-- `x` and `y` are infinitely close. -/
def Approx {E : Type*} [SeminormedAddCommGroup E] (x y : Hyp E) : Prop :=
  (x - y).Tendsto (𝓝 0)

@[inherit_doc] scoped infix:50 " ≈ₕ " => Approx

section Extension

variable {α β γ : Type*}

lemma ext_comp (f : β → γ) (g : α → β) (ξ : Hyp α) :
    ext f (ext g ξ) = ext (fun x => f (g x)) ξ :=
  Germ.map_map f g ξ

lemma ext_const (ξ : Hyp α) (c : β) : ext (fun _ => c) ξ = std c :=
  Germ.inductionOn ξ fun _ => rfl

lemma ext_id (ξ : Hyp α) : ext (fun x => x) ξ = ξ :=
  Germ.inductionOn ξ fun _ => rfl

lemma ext_add [Add β] (f g : α → β) (ξ : Hyp α) :
    ext (fun x => f x + g x) ξ = ext f ξ + ext g ξ :=
  Germ.inductionOn ξ fun _ => rfl

lemma ext_sub [Sub β] (f g : α → β) (ξ : Hyp α) :
    ext (fun x => f x - g x) ξ = ext f ξ - ext g ξ :=
  Germ.inductionOn ξ fun _ => rfl

lemma ext_mul [Mul β] (f g : α → β) (ξ : Hyp α) :
    ext (fun x => f x * g x) ξ = ext f ξ * ext g ξ :=
  Germ.inductionOn ξ fun _ => rfl

lemma imem_univ (ξ : Hyp α) : IMem ξ univ :=
  Germ.inductionOn ξ fun _ => Germ.liftPred_coe.mpr (Eventually.of_forall fun _ => trivial)

/-- Transfer: `∀ x ∈ s, f x ∈ t` gives `∀ ξ ∈ *s, *f ξ ∈ *t`. -/
lemma transfer_mem {f : α → β} {s : Set α} {t : Set β} (h : ∀ x ∈ s, f x ∈ t) {ξ : Hyp α}
    (hξ : IMem ξ s) : IMem (ext f ξ) t := sorry

/-- Transfer: `∀ x ∈ s, f x ≤ g x` gives `∀ ξ ∈ *s, *f ξ ≤ *g ξ`. -/
lemma transfer_le {f g : α → ℝ} {s : Set α} (h : ∀ x ∈ s, f x ≤ g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ ≤ ext g ξ := sorry

/-- Transfer: `∀ x ∈ s, f x = g x` gives `∀ ξ ∈ *s, *f ξ = *g ξ`. -/
lemma transfer_eq {f g : α → β} {s : Set α} (h : ∀ x ∈ s, f x = g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ = ext g ξ := sorry

end Extension

section Approx

variable {E : Type*} [NormedAddCommGroup E]

lemma approx_refl (x : Hyp E) : x ≈ₕ x := sorry

lemma Approx.symm {x y : Hyp E} (h : x ≈ₕ y) : y ≈ₕ x := sorry

lemma Approx.trans {x y z : Hyp E} (hxy : x ≈ₕ y) (hyz : y ≈ₕ z) : x ≈ₕ z := sorry

lemma approx_iff_sub {x y : Hyp E} : x ≈ₕ y ↔ x - y ≈ₕ std 0 := sorry

lemma Approx.add_std {x y : Hyp E} {a b : E} (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) :
    x + y ≈ₕ std (a + b) := sorry

lemma Approx.sub_std {x y : Hyp E} {a b : E} (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) :
    x - y ≈ₕ std (a - b) := sorry

lemma Approx.mul_std {R : Type*} [NormedRing R] {x y : Hyp R} {a b : R}
    (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) : x * y ≈ₕ std (a * b) := sorry

/-- Standard points that are infinitely close are equal. -/
lemma eq_of_std_approx {a b : E} (h : std a ≈ₕ std b) : a = b := sorry

/-- A standard multiple of an infinitesimal is infinitesimal. -/
lemma approx_zero_of_norm_le {F : Type*} [NormedAddCommGroup F] {x : Hyp E} {y : Hyp F}
    {c : ℝ} (hxy : ext norm x ≤ std c * ext norm y) (hy : y ≈ₕ std 0) : x ≈ₕ std 0 := sorry

/-- Squeeze: a hyperreal between two that are infinitely close to `t` is too. -/
lemma approx_of_le_of_le {lo ξ hi : Hyp ℝ} {t : ℝ} (hlo : lo ≤ ξ) (hhi : ξ ≤ hi)
    (hlot : lo ≈ₕ std t) (hhit : hi ≈ₕ std t) : ξ ≈ₕ std t := sorry

/-- In a proper space, a finite element has a standard part. -/
lemma exists_std [ProperSpace E] {x : Hyp E} {C : ℝ} (hx : ext norm x ≤ std C) :
    ∃ a, x ≈ₕ std a := sorry

/-- Continuity: points infinitely close to `x` map to points infinitely close to `f x`. -/
lemma approx_ext_of_continuousWithinAt {f : ℝ → E} {s : Set ℝ} {x : ℝ}
    (hf : ContinuousWithinAt f s x) {ξ : Hyp ℝ} (hξs : IMem ξ s) (hξ : ξ ≈ₕ std x) :
    ext f ξ ≈ₕ std (f x) := sorry

/-- Derivative: difference quotients over positive infinitesimals are infinitely close to it. -/
lemma approx_slope_of_hasDerivAt [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' x) {ε : Hyp ℝ} (hpos : IMem ε (Ioi 0)) (hε : ε ≈ₕ std 0) :
    ext (fun h => h⁻¹ • (f (x + h) - f x)) ε ≈ₕ std f' := sorry

/-- `c / (ω + 1)` is infinitesimal. -/
lemma approx_div_omega (c : ℝ) : ext (fun n : ℕ => c / (n + 1 : ℝ)) ω ≈ₕ std 0 := sorry

end Approx

/-! ## The semigroup theorem -/

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- **Continuous semigroups are exponentials**, in nonstandard language. -/
theorem exists_eq_exp_of_semigroup [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  obtain ⟨δ, hδ, C, hbound⟩ := exists_bounded_generators M (hcont 0 (by simp)) h0 hadd
  -- A positive infinitesimal step `ε = δ / (ω + 1)`.
  let e : ℕ → ℝ := fun n => δ / (n + 1 : ℝ)
  let ε : Hyp ℝ := ext e ω
  have hεpos : IMem ε (Ioi 0) :=
    transfer_mem (fun n _ => show e n ∈ Ioi 0 from div_pos hδ (by positivity)) (imem_univ ω)
  have hε : ε ≈ₕ std 0 := approx_div_omega δ
  -- `(*M ε - 1) / ε` is finite, so it has a standard part `a`.
  let q : ℝ → A := fun h => h⁻¹ • (M h - 1)
  have hQ : ext norm (ext q ε) ≤ std C := by
    change ext norm (ext q (ext e ω)) ≤ std C
    rw [ext_comp, ext_comp, ← ext_const ω C]
    exact transfer_le (fun n _ => hbound n) (imem_univ ω)
  obtain ⟨a, ha⟩ := exists_std hQ
  refine ⟨a, fun t ht => ?_⟩
  let E : ℝ → A := fun s => exp (s • -a)
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_exp_smul_const (-a) s).continuousAt
  have hEadd : ∀ s u, E (s + u) = E s * E u := fun s u => by
    simp only [E, add_smul]
    exact exp_add_of_commute (((Commute.refl (-a)).smul_left s).smul_right u)
  have hE0 : E 0 = 1 := by simp [E]
  let F : ℝ → A := fun s => M s * E s
  obtain ⟨C', hC'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hE.continuousOn (s := Icc 0 t))
  -- One step changes `F` by `ε g` with `g = (*M ε * *E ε - 1) / ε ≈ a - a = 0`.
  let g : ℝ → A := fun h => h⁻¹ • (M h * E h - 1)
  let slope : ℝ → A := fun h => h⁻¹ • (E (0 + h) - E 0)
  have hgsplit : ext g ε = ext q ε * ext E ε + ext slope ε := by
    rw [← ext_mul, ← ext_add]
    refine transfer_eq (fun h _ => ?_) (imem_univ ε)
    simp only [g, q, slope, zero_add, hE0, smul_sub, sub_mul, smul_mul_assoc, one_mul]
    abel
  have hg : ext g ε ≈ₕ std 0 := by
    have hEε : ext E ε ≈ₕ std (E 0) :=
      approx_ext_of_continuousWithinAt hE.continuousAt.continuousWithinAt (imem_univ ε) hε
    have hslope : ext slope ε ≈ₕ std (-a * E 0) :=
      approx_slope_of_hasDerivAt (hasDerivAt_exp_smul_const' (-a) 0) hεpos hε
    have h := (ha.mul_std hEε).add_std hslope
    rwa [hE0, mul_one, mul_one, add_neg_cancel, ← hgsplit] at h
  -- Telescoping over `K = ⌊t / ε⌋` steps: `*F (K ε) ≈ 1`.
  let K : ℝ → ℝ := fun h => (⌊t / h⌋₊ : ℝ) * h
  have hFK : ext (fun h => F (K h)) ε ≈ₕ std 1 := by
    rw [approx_iff_sub, ← ext_const ε (1 : A), ← ext_sub]
    refine approx_zero_of_norm_le (c := t * (C' * D)) ?_ hg
    rw [ext_comp norm (fun h => F (K h) - 1) ε, ext_comp norm g ε,
      ← ext_const ε (t * (C' * D)), ← ext_mul]
    refine transfer_le (fun h hh => ?_) hεpos
    simpa [mul_assoc] using norm_telescope_le M E h0 hE0 hadd hEadd ht hC' hD hh
  -- `K ε ≈ t`, so `*F (K ε) ≈ F t`, and `F t = 1`.
  have hKt : ext K ε ≈ₕ std t := by
    refine approx_of_le_of_le (lo := ext (fun h => t - h) ε) (hi := ext (fun _ => t) ε)
      (transfer_le (fun h hh => ?_) hεpos) (transfer_le (fun h hh => ?_) hεpos) ?_ ?_
    · have := Nat.lt_floor_add_one (t / h)
      rw [div_lt_iff₀ hh, add_one_mul] at this
      simp only [K]
      linarith
    · exact (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ht (le_of_lt hh)))
    · have h := (approx_refl (std t)).sub_std hε
      rw [sub_zero] at h
      rwa [ext_sub (fun _ => t) (fun h => h) ε, ext_const, ext_id]
    · rw [ext_const]
      exact approx_refl _
  have hKmem : IMem (ext K ε) (Icc 0 t) := transfer_mem (f := K) (t := Icc 0 t) (fun h hh =>
    ⟨mul_nonneg (Nat.cast_nonneg _) (le_of_lt hh),
      (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ht (le_of_lt hh)))⟩) hεpos
  have hFt : ext (fun h => F (K h)) ε ≈ₕ std (F t) := by
    have h := approx_ext_of_continuousWithinAt
      (((hcont.mono Icc_subset_Ici_self).mul hE.continuousOn) t ⟨ht, le_rfl⟩) hKmem hKt
    rwa [ext_comp] at h
  have hF1 : F t = 1 := eq_of_std_approx (hFt.symm.trans hFK)
  have hinv : E t * exp (t • a) = 1 := by
    rw [← exp_add_of_commute (((Commute.refl a).neg_left.smul_left t).smul_right t),
      smul_neg, neg_add_cancel, exp_zero]
  calc
    M t = M t * (E t * exp (t • a)) := by rw [hinv, mul_one]
    _ = F t * exp (t • a) := by rw [← mul_assoc]
    _ = exp (t • a) := by rw [hF1, one_mul]

end Experiments.NSA
