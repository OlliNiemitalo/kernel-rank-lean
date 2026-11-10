import Mathlib

/-!
# A small interface for nonstandard analysis

Mathlib models the hyperreals as an ultrapower: germs of real sequences along the ultrafilter
`hyperfilter ℕ`. This file gives the same construction for any type the vocabulary of
nonstandard analysis:

* `Hyp α` is the ultrapower `*α`, `std x` the standard copy of `x`, and `ext f` the natural
  extension `*f` of a function `f`.
* `IMem ξ s` is internal membership `ξ ∈ *s`.
* `x ≈ₕ y` means that `x` and `y` are infinitely close: `x - y` is infinitesimal.
* `transfer_mem`, `transfer_le` and `transfer_eq` are one-variable instances of the transfer
  principle: a statement about all points of a set `s` holds for all points of `*s`.
* `exists_std` gives standard parts in finite dimensions, and the last lemmas express
  continuity and derivatives at infinitesimal scale.

Nothing here is specific to semigroups. Every proof is short, because a germ of a sequence `u`
is infinitely close to `a` exactly when `u` tends to `a` along the ultrafilter
(`approx_std_coe`): the vocabulary is a way of speaking about such limits.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace Experiments.NSA

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
    (hξ : IMem ξ s) : IMem (ext f ξ) t := by
  induction ξ using Germ.inductionOn with
  | h u => exact Germ.liftPred_coe.mpr ((Germ.liftPred_coe.mp hξ).mono fun n => h _)

/-- Transfer: `∀ x ∈ s, f x ≤ g x` gives `∀ ξ ∈ *s, *f ξ ≤ *g ξ`. -/
lemma transfer_le {f g : α → ℝ} {s : Set α} (h : ∀ x ∈ s, f x ≤ g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ ≤ ext g ξ := by
  induction ξ using Germ.inductionOn with
  | h u => exact Germ.coe_le.mpr ((Germ.liftPred_coe.mp hξ).mono fun n => h _)

/-- Transfer: `∀ x ∈ s, f x = g x` gives `∀ ξ ∈ *s, *f ξ = *g ξ`. -/
lemma transfer_eq {f g : α → β} {s : Set α} (h : ∀ x ∈ s, f x = g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ = ext g ξ := by
  induction ξ using Germ.inductionOn with
  | h u => exact Germ.coe_eq.mpr ((Germ.liftPred_coe.mp hξ).mono fun n => h _)

end Extension

section Approx

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- For germs of sequences, `≈ₕ` is convergence of the difference along the ultrafilter. -/
lemma approx_coe {u v : ℕ → E} :
    (u : Hyp E) ≈ₕ (v : Hyp E) ↔ Tendsto (fun n => u n - v n) (hyperfilter ℕ) (𝓝 0) :=
  Iff.rfl

/-- The germ of `u` is infinitely close to `a` exactly when `u` tends to `a` along the
ultrafilter: `a` is the standard part of `u`. -/
lemma approx_std_coe {u : ℕ → E} {a : E} :
    (u : Hyp E) ≈ₕ std a ↔ Tendsto u (hyperfilter ℕ) (𝓝 a) :=
  tendsto_sub_nhds_zero_iff

lemma approx_refl (x : Hyp E) : x ≈ₕ x := by
  induction x using Germ.inductionOn with
  | h u => exact approx_coe.mpr (by simp)

lemma Approx.symm {x y : Hyp E} (h : x ≈ₕ y) : y ≈ₕ x := by
  induction x, y using Germ.inductionOn₂ with
  | h u v => exact approx_coe.mpr (by simpa using (approx_coe.mp h).neg)

lemma Approx.trans {x y z : Hyp E} (hxy : x ≈ₕ y) (hyz : y ≈ₕ z) : x ≈ₕ z := by
  induction x, y, z using Germ.inductionOn₃ with
  | H u v w => exact approx_coe.mpr (by simpa using (approx_coe.mp hxy).add (approx_coe.mp hyz))

lemma approx_iff_sub {x y : Hyp E} : x ≈ₕ y ↔ x - y ≈ₕ std 0 := by
  induction x, y using Germ.inductionOn₂ with
  | h u v => exact approx_coe.trans (approx_std_coe (u := fun n => u n - v n)).symm

lemma Approx.sub_std {x y : Hyp E} {a b : E} (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) :
    x - y ≈ₕ std (a - b) := by
  induction x, y using Germ.inductionOn₂ with
  | h u v => exact approx_std_coe.mpr ((approx_std_coe.mp hx).sub (approx_std_coe.mp hy))

lemma Approx.mul_std {R : Type*} [NormedRing R] {x y : Hyp R} {a b : R}
    (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) : x * y ≈ₕ std (a * b) := by
  induction x, y using Germ.inductionOn₂ with
  | h u v => exact approx_std_coe.mpr ((approx_std_coe.mp hx).mul (approx_std_coe.mp hy))

/-- Standard points that are infinitely close are equal. -/
lemma eq_of_std_approx {a b : E} (h : std a ≈ₕ std b) : a = b :=
  tendsto_nhds_unique tendsto_const_nhds (approx_std_coe.mp h)

/-- A finite multiple of an infinitesimal is infinitesimal. -/
lemma approx_zero_of_norm_le {x : Hyp E} {y : Hyp F} {k : Hyp ℝ} {c : ℝ} (hk : k ≈ₕ std c)
    (hxy : ext norm x ≤ k * ext norm y) (hy : y ≈ₕ std 0) : x ≈ₕ std 0 := by
  induction x, y, k using Germ.inductionOn₃ with
  | H u v κ =>
    refine approx_std_coe.mpr (squeeze_zero_norm' (Germ.coe_le.mp hxy) ?_)
    simpa using (approx_std_coe.mp hk).mul (approx_std_coe.mp hy).norm

/-- Squeeze: a hyperreal between two that are infinitely close to `t` is too. -/
lemma approx_of_le_of_le {lo ξ hi : Hyp ℝ} {t : ℝ} (hlo : lo ≤ ξ) (hhi : ξ ≤ hi)
    (hlot : lo ≈ₕ std t) (hhit : hi ≈ₕ std t) : ξ ≈ₕ std t := by
  induction lo, ξ, hi using Germ.inductionOn₃ with
  | H l u h =>
    exact approx_std_coe.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (approx_std_coe.mp hlot) (approx_std_coe.mp hhit) (Germ.coe_le.mp hlo) (Germ.coe_le.mp hhi))

/-- In a proper space, a bounded element has a standard part, with the same bound: a bounded
sequence in a compact ball converges along the ultrafilter. -/
lemma exists_std [ProperSpace E] {x : Hyp E} {C : ℝ} (hx : ext norm x ≤ std C) :
    ∃ a, ‖a‖ ≤ C ∧ x ≈ₕ std a := by
  induction x using Germ.inductionOn with
  | h u =>
    obtain ⟨a, ha, hu⟩ := (isCompact_closedBall (0 : E) C).ultrafilter_le_nhds
      (.map u (hyperfilter ℕ)) (le_principal_iff.mpr
        ((Germ.coe_le.mp hx).mono fun n hn => mem_closedBall_zero_iff.mpr hn))
    exact ⟨a, mem_closedBall_zero_iff.mp ha, approx_std_coe.mpr hu⟩

/-- Continuity: points of `*s` infinitely close to `x` map to points infinitely close to
`f x`. -/
lemma approx_ext_of_continuousWithinAt {f : F → E} {s : Set F} {x : F}
    (hf : ContinuousWithinAt f s x) {ξ : Hyp F} (hξs : IMem ξ s) (hξ : ξ ≈ₕ std x) :
    ext f ξ ≈ₕ std (f x) := by
  induction ξ using Germ.inductionOn with
  | h u =>
    exact approx_std_coe.mpr (hf.tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨approx_std_coe.mp hξ, Germ.liftPred_coe.mp hξs⟩))

/-- Derivative: difference quotients over positive infinitesimals are infinitely close to it. -/
lemma approx_slope_of_hasDerivAt [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' x) {ε : Hyp ℝ} (hpos : IMem ε (Ioi 0)) (hε : ε ≈ₕ std 0) :
    ext (fun h => h⁻¹ • (f (x + h) - f x)) ε ≈ₕ std f' := by
  induction ε using Germ.inductionOn with
  | h e =>
    exact approx_std_coe.mpr (hf.tendsto_slope_zero_right.comp
      (tendsto_nhdsWithin_iff.mpr ⟨approx_std_coe.mp hε, Germ.liftPred_coe.mp hpos⟩))

/-- `c / (ω + 1)` is infinitesimal. -/
lemma approx_div_omega (c : ℝ) : ext (fun n : ℕ => c / (n + 1 : ℝ)) ω ≈ₕ std 0 := by
  refine approx_std_coe.mpr (Tendsto.mono_left ?_ Nat.hyperfilter_le_atTop)
  simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c

end Approx

end Experiments.NSA
