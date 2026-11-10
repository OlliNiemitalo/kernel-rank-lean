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
of it (`transfer_mem`, `transfer_le`, `transfer_eq`). For that reason the scale `η` and all
other quantities are ordinary functions of the step `h`, evaluated at the infinitesimal `ε`.

For a proof of the same theorem with no `sorry`, see `NonstandardSemigroup.lean`, which works
with sequences along the ultrafilter instead. Its header explains the argument.
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

lemma approx_refl (x : Hyp E) : x ≈ₕ x := sorry

lemma Approx.symm {x y : Hyp E} (h : x ≈ₕ y) : y ≈ₕ x := sorry

lemma Approx.trans {x y z : Hyp E} (hxy : x ≈ₕ y) (hyz : y ≈ₕ z) : x ≈ₕ z := sorry

lemma approx_iff_sub {x y : Hyp E} : x ≈ₕ y ↔ x - y ≈ₕ std 0 := sorry

lemma Approx.sub_std {x y : Hyp E} {a b : E} (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) :
    x - y ≈ₕ std (a - b) := sorry

lemma Approx.mul_std {R : Type*} [NormedRing R] {x y : Hyp R} {a b : R}
    (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) : x * y ≈ₕ std (a * b) := sorry

/-- Standard points that are infinitely close are equal. -/
lemma eq_of_std_approx {a b : E} (h : std a ≈ₕ std b) : a = b := sorry

/-- A finite multiple of an infinitesimal is infinitesimal. -/
lemma approx_zero_of_norm_le {x : Hyp E} {y : Hyp F} {k : Hyp ℝ} {c : ℝ} (hk : k ≈ₕ std c)
    (hxy : ext norm x ≤ k * ext norm y) (hy : y ≈ₕ std 0) : x ≈ₕ std 0 := sorry

/-- Squeeze: a hyperreal between two that are infinitely close to `t` is too. -/
lemma approx_of_le_of_le {lo ξ hi : Hyp ℝ} {t : ℝ} (hlo : lo ≤ ξ) (hhi : ξ ≤ hi)
    (hlot : lo ≈ₕ std t) (hhit : hi ≈ₕ std t) : ξ ≈ₕ std t := sorry

/-- In a proper space, a bounded element has a standard part, with the same bound. -/
lemma exists_std [ProperSpace E] {x : Hyp E} {C : ℝ} (hx : ext norm x ≤ std C) :
    ∃ a, ‖a‖ ≤ C ∧ x ≈ₕ std a := sorry

/-- Continuity: points of `*s` infinitely close to `x` map to points infinitely close to
`f x`. -/
lemma approx_ext_of_continuousWithinAt {f : F → E} {s : Set F} {x : F}
    (hf : ContinuousWithinAt f s x) {ξ : Hyp F} (hξs : IMem ξ s) (hξ : ξ ≈ₕ std x) :
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
  -- A positive infinitesimal step `ε = 1 / (ω + 1)`.
  let e : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let ε : Hyp ℝ := ext e ω
  have hεpos : IMem ε (Ioi 0) :=
    transfer_mem (fun (n : ℕ) _ => show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity) (imem_univ ω)
  have hε : ε ≈ₕ std 0 := approx_div_omega 1
  -- The scale `η = ε + ‖*M ε - 1‖` is a positive infinitesimal, because `*M ε ≈ M 0`.
  let η : ℝ → ℝ := fun h => h + ‖M h - 1‖
  have hηh : ∀ h, 0 < h → 0 < η h := fun h hh => add_pos_of_pos_of_nonneg hh (norm_nonneg _)
  have hηpos : IMem (ext η ε) (Ioi 0) := transfer_mem (f := η) hηh hεpos
  have hη : ext η ε ≈ₕ std 0 := by
    have hc : ContinuousWithinAt η (Ici 0) 0 :=
      continuousWithinAt_id.add ((hcont 0 (by simp)).sub continuousWithinAt_const).norm
    have hmem : IMem ε (Ici 0) := by
      simpa only [ext_id] using
        transfer_mem (f := fun x => x) (fun x hx => mem_Ici.mpr (mem_Ioi.mp hx).le) hεpos
    have h := approx_ext_of_continuousWithinAt hc hmem hε
    rwa [show η 0 = 0 by simp [η, h0]] at h
  -- On that scale the change `q` is finite, so it has a standard part `B`, and the time is
  -- infinitely close to `a = 1 - ‖B‖`.
  let q : ℝ → A := fun h => (η h)⁻¹ • (M h - 1)
  have hsum : ∀ h, 0 < h → h / η h = 1 - ‖q h‖ := fun h hh => by
    have := (hηh h hh).ne'
    simp only [q, norm_smul, norm_inv, Real.norm_of_nonneg (hηh h hh).le]
    field_simp
    simp only [η]
    ring
  have hq : ext norm (ext q ε) ≤ std 1 := by
    rw [ext_comp, ← ext_const ε (1 : ℝ)]
    exact transfer_le (fun h hh => by
      linarith [hsum h hh, div_nonneg (le_of_lt hh) (hηh h hh).le]) hεpos
  obtain ⟨B, hB1, hB⟩ := exists_std hq
  let a : ℝ := 1 - ‖B‖
  have ha : ext (fun h => h / η h) ε ≈ₕ std a := by
    have h1 : ext (fun h => h / η h) ε = std 1 - ext norm (ext q ε) := by
      rw [ext_comp norm q ε, ← ext_const ε (1 : ℝ), ← ext_sub]
      exact transfer_eq hsum hεpos
    rw [h1]
    exact (approx_refl _).sub_std
      (approx_ext_of_continuousWithinAt continuous_norm.continuousWithinAt (imem_univ _) hB)
  -- The exponential `E u = exp (u B)` takes the same step on that scale, to first order.
  let E : ℝ → A := fun u => exp (u • B)
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun u =>
    (hasDerivAt_exp_smul_const B u).continuousAt
  have hEadd : ∀ u v, E (u + v) = E u * E v := fun u v => by
    simp only [E, add_smul]
    exact exp_add_of_commute (((Commute.refl B).smul_left u).smul_right v)
  have hE0 : E 0 = 1 := by simp [E]
  let slope : ℝ → A := fun k => k⁻¹ • (E (0 + k) - E 0)
  have hslope : ext slope (ext η ε) ≈ₕ std B := by
    have h : ext slope (ext η ε) ≈ₕ std (B * E 0) :=
      approx_slope_of_hasDerivAt (hasDerivAt_exp_smul_const' B 0) hηpos hη
    rwa [hE0, mul_one] at h
  let g : ℝ → A := fun h => (η h)⁻¹ • (M h - E (η h))
  have hg : ext g ε ≈ₕ std 0 := by
    have hsplit : ext g ε = ext q ε - ext slope (ext η ε) := by
      rw [ext_comp slope η ε, ← ext_sub]
      refine transfer_eq (fun h _ => ?_) (imem_univ ε)
      simp only [g, q, slope, zero_add, hE0, smul_sub]
      abel
    have h := hB.sub_std hslope
    rwa [sub_self, ← hsplit] at h
  -- Euler's step: `M (s a) = E s` for standard `s ≥ 0`.
  have hmain : ∀ s, 0 ≤ s → M (s * a) = E s := fun s hs => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hcont.mono (Icc_subset_Ici_self : Icc 0 s ⊆ Ici 0))
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hE.continuousOn (s := Icc 0 s))
    -- Take `N = ⌊s / η⌋` steps. `M` arrives at the time `T = N ε` and `E` at `K = N η`.
    let K : ℝ → ℝ := fun k => (⌊s / k⌋₊ : ℝ) * k
    let T : ℝ → ℝ := fun h => (⌊s / η h⌋₊ : ℝ) * h
    have hKs : ∀ k, 0 < k → K k ≤ s := fun k hk =>
      (le_div_iff₀ hk).mp (Nat.floor_le (div_nonneg hs (le_of_lt hk)))
    -- The times: `K ≈ s` and `T ≈ s a`.
    have hK : ext K (ext η ε) ≈ₕ std s := by
      refine approx_of_le_of_le (lo := ext (fun k => s - k) (ext η ε))
        (hi := ext (fun _ => s) (ext η ε))
        (transfer_le (fun k hk => ?_) hηpos) (transfer_le hKs hηpos) ?_ ?_
      · have := Nat.lt_floor_add_one (s / k)
        rw [div_lt_iff₀ hk, add_one_mul] at this
        simp only [K]
        linarith
      · have h := (approx_refl (std s)).sub_std hη
        rw [sub_zero] at h
        rwa [ext_sub (fun _ => s) (fun k => k) (ext η ε), ext_const, ext_id]
      · rw [ext_const]
        exact approx_refl _
    have hT : ext T ε ≈ₕ std (s * a) := by
      have h1 : ext T ε = ext K (ext η ε) * ext (fun h => h / η h) ε := by
        rw [ext_comp K η ε, ← ext_mul]
        refine transfer_eq (fun h hh => ?_) hεpos
        have := (hηh h hh).ne'
        simp only [T, K]
        field_simp
      rw [h1]
      exact hK.mul_std ha
    have hMT : ext M (ext T ε) ≈ₕ std (M (s * a)) :=
      approx_ext_of_continuousWithinAt
        (hcont _ (mul_nonneg hs (sub_nonneg.mpr hB1)))
        (transfer_mem (f := T) (fun h hh =>
          mem_Ici.mpr (mul_nonneg (Nat.cast_nonneg _) (mem_Ioi.mp hh).le)) hεpos) hT
    have hEK : ext E (ext K (ext η ε)) ≈ₕ std (E s) :=
      approx_ext_of_continuousWithinAt hE.continuousAt.continuousWithinAt (imem_univ _) hK
    -- Replacing the steps of `M` by those of `E` changes the result by `K` times an
    -- infinitesimal.
    have hrepl : ext M (ext T ε) ≈ₕ ext E (ext K (ext η ε)) := by
      rw [approx_iff_sub, ext_comp M T ε, ext_comp K η ε, ext_comp E _ ε, ← ext_sub]
      have hk : ext K (ext η ε) * std (C * D) ≈ₕ std (s * (C * D)) :=
        hK.mul_std (approx_refl _)
      refine approx_zero_of_norm_le hk ?_ hg
      rw [ext_comp norm (fun h => M (T h) - E (K (η h))) ε, ext_comp norm g ε, ext_comp K η ε,
        ← ext_const ε (C * D), ← ext_mul, ← ext_mul]
      refine transfer_le (fun h hh => ?_) hεpos
      have hη0 := hηh h hh
      have h := norm_replace_steps_le M E h0 hadd (fun u v _ _ => hEadd u v) hC hD
        (le_of_lt hh) hη0.le ⌊s / η h⌋₊ le_rfl
        ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
          (Nat.cast_nonneg _)).trans (hKs _ hη0)) (by simpa using hKs _ hη0)
      simp only [hE0, mul_one, add_zero] at h
      have := hη0.ne'
      simp only [g, K, T, norm_smul, norm_inv, Real.norm_of_nonneg hη0.le]
      refine h.trans_eq ?_
      field_simp
    exact eq_of_std_approx ((hMT.symm.trans hrepl).trans hEK)
  -- The semigroup is not infinitely fast: `a = 0` would give `E s = 1`, so `B = 0`.
  have ha0 : a ≠ 0 := fun h => by
    have hz : ext slope (ext η ε) = std 0 := by
      rw [← ext_const (ext η ε) (0 : A)]
      refine transfer_eq (fun k hk => ?_) hηpos
      simp only [slope, zero_add, hE0, ← hmain k (le_of_lt hk), h, mul_zero, h0, sub_self,
        smul_zero]
    have hB0 : B = 0 := (eq_of_std_approx (hz ▸ hslope)).symm
    simp [a, hB0] at h
  have hapos : 0 < a := lt_of_le_of_ne (sub_nonneg.mpr hB1) (Ne.symm ha0)
  refine ⟨a⁻¹ • B, fun t ht => ?_⟩
  have h := hmain (t / a) (div_nonneg ht hapos.le)
  rw [div_mul_cancel₀ t ha0] at h
  rw [h, smul_smul, div_eq_mul_inv]

end Experiments.NSA
