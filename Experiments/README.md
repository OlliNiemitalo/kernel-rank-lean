# Alternative proofs of the semigroup step

One step of the main proof shows that a one-parameter semigroup `M`, with
`M (s + t) = M s * M t` and `M 0 = 1`, that is continuous on `[0, ∞)` is an exponential:
`M t = exp (t A)`. Translation of the profile is such a semigroup, so this step produces the
generator `A`. The main proof, [Semigroup.lean](../KernelRankLean/Semigroup.lean), smooths `M`
with an integral. It works in any Banach algebra.

This directory and [Isabelle](../Isabelle) hold other proofs of that step. None of them is used
by the main proof. All of them work in finite-dimensional algebras only, and all are complete:
no `sorry` in Lean, no oracle in Isabelle.

They obtain the generator `A` from the difference quotients `(M h - 1) / h` for small `h`, so
these quotients must stay bounded. The finite-difference proof proves that first. The
nonstandard proofs need no such bound. [Translation.lean](Translation.lean) applies the
finite-difference proof and the first nonstandard Lean proof to the translation semigroup.

## Finite differences

[GeneratorBound.lean](GeneratorBound.lean): if `M` stays within `1/2` of `1` on `[0, δ]`,
geometric sums bound the difference quotients for `h = δ / n`.
[FiniteDifferenceSemigroup.lean](FiniteDifferenceSemigroup.lean): in finite dimensions, a
subsequence of the bounded quotients converges to some `A`. Along it, the difference quotients
of `M t * exp (-t A)` tend to `0` at every point. A mean-value theorem for one-sided difference
quotients then shows that this product is constant.

## Nonstandard analysis, after Euler

Fix a positive infinitesimal step `ε`. In the time `ε` the semigroup changes by `x = M ε - 1`.
If the quotient `x / ε` is finite, it has a standard part `A`. One step of `M` then differs from
one step of `exp (t A)` by `ε` times an infinitesimal. Over `⌊t / ε⌋` steps these differences
add up to an infinitesimal, so `M t = exp (t A)`. This is Euler's step.

The proof does not bound `x / ε` beforehand: Euler's step itself shows that it is finite.
Measure the time and the change on the common scale `η = ε + ‖x‖`. As
`ε / η + ‖x / η‖ = 1`, both are finite without any estimate: `x / η` has a standard part `B`,
and `ε / η` is infinitely close to `a = 1 - ‖B‖`. The pair `(a, B)` is the generator in
homogeneous coordinates: `A = B / a`, once `a ≠ 0` is known. Compare `M`, taking steps of size
`ε`, with `E s = exp (s B)`, taking steps of size `η`. Their single steps differ by `η` times an
infinitesimal. After `N` steps with `s - η ≤ N η ≤ s`, their times are infinitely close to
`s a` and `s`. Controlling the accumulated error gives `M (s a) = exp (s B)`.
Now `a = 0` would mean `exp (s B) = M 0 = 1` for all `s ≥ 0`, so `B = 0` and `a = 1`. Hence
`a ≠ 0`, and `M t = exp (t B / a)`.

The argument has three formalizations. They differ in their language and in how they control
the accumulated error.

### Isabelle/HOL

[Semigroup_NSA.thy](../Isabelle/Semigroup_NSA.thy). Isabelle's `HOL-Nonstandard_Analysis`
library provides hyperreals, hypernatural numbers and nonstandard vectors as an ultrapower, a
`transfer` method, infinite closeness `≈`, standard parts of finite hyperreals, and nonstandard
characterizations of limits.

The ordinary estimate is purely algebraic: if `‖u‖, ‖v‖ ≤ exp h` and `h ≥ 0`, then
`‖uⁿ - vⁿ‖ ≤ n exp(n h) ‖u - v‖`. The proof uses
`uⁿ⁺¹ - vⁿ⁺¹ = u (uⁿ - vⁿ) + (u - v) vⁿ`, with no commutativity assumption. For `u = M ε` and
`v = exp (η B)`, the normalization gives both norm bounds with `h = η`. Transfer makes the
accumulated error at most `N η exp(N η) ‖(u - v) / η‖`, for a hypernatural number `N` of steps,
and this is infinitesimal.

The proof adds two facts that the library lacks: standard parts of bounded vectors in
finite-dimensional (Heine–Borel) spaces, and continuity at nonnegative arguments, for which it
extends `M` to the whole line by `M (max t 0)` and uses the library's nonstandard continuity.

The power estimate uses `‖1‖ = 1`, which Isabelle's `real_normed_algebra_1` supplies. The Lean
theorems do not assume it, so the Lean proofs control the error differently.

### Lean, with sequences

[NonstandardSemigroup.lean](NonstandardSemigroup.lean). Mathlib has hyperreals, as sequences
along an ultrafilter, but no transfer principle, so this proof works with those sequences
directly: "infinitely close" becomes convergence along the ultrafilter.

Euler's step (`eq_of_infinitesimal_steps`) compares two arbitrary continuous semigroups, with
step sizes `δ ≤ η` and `δ / η` tending to `a`, along an arbitrary filter. It bounds both
semigroups on compact time intervals and replaces the steps of one by those of the other, one
at a time (`norm_replace_steps_le`). The ultrafilter makes the standard part `B` exist without
extracting a subsequence.

### Lean, in nonstandard language

[Ultrapower.lean](Ultrapower.lean) is a small interface for nonstandard analysis: the
ultrapower `Hyp α` along `hyperfilter ℕ`, natural extensions `ext f`, internal membership, the
relation `x ≈ₕ y` for "infinitely close", one-variable instances of the transfer principle,
standard parts in finite dimensions, and continuity and derivatives at infinitesimal scale.
Nothing in it is specific to semigroups.

[UltrapowerSemigroup.lean](UltrapowerSemigroup.lean) proves the theorem in that vocabulary,
the way a nonstandard analyst would write it. It follows the Lean proof with sequences and
shares its estimate `norm_replace_steps_le`. With one-variable transfer only, the scale `η`,
the number of steps and all other quantities are ordinary functions of the step, evaluated at
the infinitesimal `ε`.

## Comparison

Physical lines include comments and blank lines; nonblank lines exclude whitespace-only lines.
Every helper counts in full.

| Proof of the semigroup step | Files | Physical lines | Nonblank lines |
|---|---|---:|---:|
| Integral smoothing (used by the main proof) | `Semigroup.lean` | 96 | 87 |
| Finite differences | `GeneratorBound.lean` + `FiniteDifferenceSemigroup.lean` | 256 | 233 |
| Nonstandard, Lean, with sequences | `NonstandardSemigroup.lean` | 206 | 190 |
| Nonstandard, Lean, in nonstandard language | `UltrapowerSemigroup.lean` + shared estimate + `Ultrapower.lean` | 399 | 344 |
| Nonstandard, Isabelle/HOL | `Semigroup_NSA.thy` | 275 | 253 |

The bound on the difference quotients, `GeneratorBound.lean`, is 124 lines (112 nonblank) of
the finite-difference proof.

The proof in nonstandard language splits into the interface `Ultrapower.lean` (195 lines, 150
nonblank), the theorem file `UltrapowerSemigroup.lean` (169 lines, 160 nonblank, of which the
proof of the theorem is 141) and the shared estimate `norm_replace_steps_le` (35 lines, 34
nonblank).

The Lean proof with sequences and the Isabelle proof split as follows (physical / nonblank
lines):

| Part | Lean, with sequences | Isabelle/HOL |
|---|---:|---:|
| Headers, imports and overview | 45 / 33 | 29 / 24 |
| Ordinary helper lemmas: step replacement in Lean; powers in Isabelle | 35 / 34 | 44 / 40 |
| Remaining proof: Euler's step and the theorem; in Isabelle also standard parts and continuity | 126 / 123 | 202 / 189 |
| Total | 206 / 190 | 275 / 253 |

Lean separates Euler's step (58 lines) from the theorem (68 lines). Isabelle combines them in
139 lines, including the specialization of the power estimate. Its additional infrastructure
includes standard parts of bounded vectors (37 lines) and half-line continuity (22 lines);
Mathlib supplies the corresponding facts in the language of filters.

## What the comparison shows

Line counts describe these formalizations, not the mathematics in general. With that caveat:

* **The integral proof is the shortest and the most general.** It is 96 lines and holds in
  every Banach algebra. Every alternative here needs finite dimension, because the generator
  is found by compactness: as a limit of a subsequence, or as a standard part.
* **The nonstandard argument is elementary.** It uses no integration, and its only estimate
  is algebraic. This does not make it shorter: the integral proof gets integration and the
  fundamental theorem of calculus from Mathlib, at no cost in lines.
* **A library does not close the gap.** Counting the interface `Ultrapower.lean` as a library,
  as Mathlib's integration is one for the integral proof, the proof in nonstandard language
  is still 169 + 35 lines.
* **In Lean, the nonstandard vocabulary saves nothing over filters.** A germ of a sequence is
  infinitely close to `a` exactly when the sequence tends to `a` along the ultrafilter, so
  every interface lemma restates a fact about such limits. The proof with sequences is the
  same proof, and it is self-contained in 206 lines.
* **In Isabelle, transfer does real work.** It takes a hypernatural number of steps and applies
  the ordinary estimate to it as it stands. But 59 lines fill gaps in the library, and each
  transferred statement is written twice, once for the reals and once for the hyperreals.

## A purely nonstandard approach to the whole theorem

Nonstandard analysis suggests a different picture of the whole theorem, not just the semigroup
step: the continuous result is the standard part of a discrete one. None of it is formalized
beyond the semigroup step above.

**The theorem.** Since `x²` and `y²` range over `[0, ∞)`, the separable rank of `φ(x² + y²)` is
the rank of the kernel `φ(s + t)` on `[0, ∞)²`. Fix an infinitesimal step `ε > 0` and an
unlimited hypernatural `N`, and sample on the hyperfinite grid `0, ε, 2ε, …, Nε`: let
`aₖ = φ(kε)` and let `H` be the hyperfinite Hankel matrix `H_{jk} = a_{j+k}`. For continuous `φ`,
the separable rank is finite exactly when `rank H` is a standard natural number, and then the
two are equal. If every `(r + 1)`-minor of `φ(s + t)` vanishes, this transfers to the grid, so
`rank H ≤ r`. Conversely, a nonzero `r`-minor at standard points stays nonzero at nearby grid
points, by continuity, so `rank H ≥ r`.

**The proof.** A sequence whose Hankel matrix has finite rank satisfies a linear recurrence:
`aₖ = β Sᵏ v` for a square matrix `S` (Kronecker's theorem). `S` advances the grid by one
infinitesimal step, so it is close to the identity; write `S = 1 + εQ`. In a suitable basis,
continuity makes `Q` finite, so it has a standard part `A`. For standard `t`, after
`n = ⌊t / ε⌋` steps, `φ(t) ≈ β Sⁿ v ≈ β exp (t A) v`, as in Euler's derivation of the
exponential function; this is the semigroup argument above. Generalized eigenvectors of `A`
then give exponential polynomials, and the exact rank is algebra. Polynomial factors such as
`t e^{μt}` appear as standard parts of combinations of nearly equal discrete roots, which is
why multiplicities enter the cost.

**Why the main proof does not use it.** Mathlib has hyperreals but no transfer principle, so
every transferred statement (ranks of hyperfinite matrices, internal spans) would need its own
proof. Kronecker's theorem for finite Hankel matrices also has boundary cases that the infinite
version avoids. The main proof gets the same realization for free: shifting acts on the span of
the translates of `φ`.
