# kernel-rank-lean

A Lean 4 / Mathlib formalization of the separable-rank theorem for circularly symmetric
blur kernels used in [kernel-optimizer](https://github.com/OlliNiemitalo/kernel-optimizer).

## The theorems

A kernel `K : (∀ i, X i) → 𝕜` on a finite family of coordinates is a sum of `N` coordinatewise
products (`IsSumOfProducts K N`) when
$K(x) = \sum_{n=0}^{N-1} \prod_i f_{n,i}(x_i)$; the least such `N` in `ℕ∞` is its *separable
rank* (`separableRank K`). On `ℝ^d` (`Fin d → ℝ`), a circularly symmetric (*radial*) kernel has
the form `x ↦ φ (∑ j, x j ^ 2)`. A *component* is `s ↦ Re (P(s) exp (λ s))` with a complex
*rate* `λ` and a nonzero polynomial `P` of degree `m - 1`, where `IsRepresentation` requires
distinct rates in the closed upper half-plane and real coefficients for real rates.

In [Main.lean](KernelRankLean/Main.lean), for `φ : ℝ → ℝ` and `ψ : ℝ → ℂ` continuous on `[0, ∞)`
and any dimension `d ≥ 2`:

1. **`d`-D finite-rank classification (`KernelRank.separableRank_radial_lt_top_iff_exists`):**
   ```lean
   separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) < ⊤ ↔
     ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s
   ```
   Restricting to a 2-D coordinate plane reduces necessity to `d = 2`; coordinatewise polynomial-
   exponential expansion gives finite `d`-way rank for every representation.

2. **Exact `d`-D complex radial rank (`KernelRank.separableRank_radial_complex_eq_iff`):**
   ```lean
   separableRank (fun x : Fin d → ℝ => ψ (∑ j, x j ^ 2)) = N ↔
     ∃ (S : Finset ℂ) (P : ℂ → ℂ[X]),
       (∀ μ ∈ S, P μ ≠ 0) ∧
       (∀ s, 0 ≤ s → ψ s = ∑ μ ∈ S, expPoly (P μ) μ s) ∧
       ∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1) = N
   ```
   A degree-`m` complex exponential polynomial `P(∑ j, s_j) exp(λ ∑ j, s_j)` splits into
   `(d - 1) m + 1` complex `d`-way products via root-of-unity interpolation on the truncated
   polynomial ring `ℂ[T] / (T^(m + 1))`, and flattened matricization together with
   Alder–Strassen substitution proves the matching lower bound (`MultiComplexRank.lean`).

3. **Exact `d`-D real radial rank (`KernelRank.separableRank_radial_eq_iff`):** in dimension
   `d ≥ 2`, a component of polynomial degree `k = deg P` costs `(d - 1) k + 1` real `d`-way
   products for a real rate (`Im λ = 0`) and `2 (d - 1) k + d` real `d`-way products for a
   nonreal conjugate-pair rate (`Im λ > 0`), summed in `multiTotalCost d cs`:
   ```lean
   separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = N ↔
     ∃ cs : List Component, IsRepresentation cs ∧
       (∀ s, 0 ≤ s → φ s = profile cs s) ∧ multiTotalCost d cs = N
   ```
   Real rates use Lagrange interpolation over `ℝ` at `(d - 1) k + 1` real nodes, while nonreal
   rates use the alternating root-of-unity polynomial-product identity (`re_coeff_prod_eq_sum_re`,
   with `R = 2 (d - 1) k + d` for `d ≥ 2`)
   $$\mathrm{Re}\!\left([X^k]\prod_{j=0}^{d-1} U_j(X)\right) = \frac{2^{d-1}}{R}\sum_{r=0}^{R-1} (-1)^r \prod_{j=0}^{d-1} \mathrm{Re}\!\left(U_j\!\left(e^{\frac{2\pi i r}{R}}\right) e^{-\frac{i\pi r (2k + 1)}{R}}\right),$$
   which reduces at `k = 0` (`R = d`, `re_prod_eq_sum_re`) to a `d`-term real product expansion
   of `Re (∏ j, z_j)` (giving `3` real terms instead of `2^(3 - 1) = 4` in 3-D), and
   Alder–Strassen degree peeling over `ℝ` proves optimality (`MultiRealRank.lean`). Specializing
   `multiTotalCost` gives:
   * **Multi-Gaussian representations (`deg P = 0`, `separableRank_radial_gaussian_profile`,
     `separableRank_radial_gaussian_eq_iff`):** exact rank `gaussianTotalCost d cs = r + d * c`
     for `r` real rates and `c` nonreal rates (so `Re(exp(i ‖x‖²))` has complex rank `2` and real
     rank `d`, showing that complexification strictly lowers `d`-way rank for `d ≥ 3`).
   * **Two dimensions (`d = 2`, `separableRank_radial_two_eq_iff`):** `multiTotalCost 2 cs =
     totalCost cs` (`k + 1` for real `λ`, `2 (k + 1)` for nonreal `λ`).

The proof in the `KernelRankLean` library is complete (no `sorry`); `#print axioms` reports
only `propext`, `Classical.choice` and `Quot.sound`. The separate `Experiments` library and the
`Isabelle` directory hold alternative proofs of one step, also complete, described
[below](#alternative-proofs-of-the-semigroup-step).

In two coordinates (`Fin 2 → α`), separable rank equals the dimension of the row span over any
field (`RowSpan.lean`), and `separableRank_ofReal` shows that allowing complex factors does not
lower the 2-way rank of a real-valued kernel, including when its rank is infinite
(`separableRank_ofReal_le` gives the one-sided inequality in every dimension).

`exists_minimal_differential_annihilator` gives another 2-D characterization for continuous
finite-rank profiles: there is a monic polynomial `p` whose degree equals the 2-D radial
kernel's rank, and `q(D) φ = 0` on `[0, ∞)` exactly when `p` divides `q`. Here `D` uses
derivatives within that half-line, including right derivatives at zero. For an
exponential-polynomial expansion, the proof computes
$p(X) = \prod_\mu (X - \mu)^{\deg P_\mu + 1}$.
Taylor expansion bounds the translate-span dimension from above. Cayley–Hamilton supplies
an annihilator whose degree equals that dimension, giving the matching lower bound.

Necessity and the 2-D exact-rank lower bound share one realization, with no choice of basis.
Translation acts on the finite-dimensional complex span of the translates of `φ`; it is a
continuous semigroup, hence `exp (t A)`. The profile is the initial vector, and evaluation at
zero reads it back out. Continuity uses a norm compatible with the pointwise topology.

## Potential applications

On a `d`-dimensional Cartesian grid, direct spatial convolution with a dense `L × ⋯ × L` kernel
evaluates `L^d` taps per grid point, whereas a sum of `R` coordinatewise products evaluates
`d R L` 1-D taps per grid point (or `O(d R)` operations independent of `L` when 1-D exponential
factors are realized recursively as causal/anti-causal IIR filters). Over `ℝ`,
`separableRank_radial_lt_top_iff_exists` shows that continuous isotropic kernels `φ(‖x‖²)` with
finite coordinatewise rank *must* be sums of polynomial-exponential components: positive real
Gaussians alone are monotone in `r²` and cannot form flat passbands or zero crossings, while
complex rates `λ = -α + i β` (`α > 0`) contribute damped radial oscillations
`exp(-α r²) cos(β r² + θ)` that can approximate oscillatory and flat-top isotropic kernels.

* **2-D circularly symmetric blur, bokeh, and optical point-spread functions.** Camera defocus
  disks, glare kernels, and Airy diffraction patterns `(J₁(r) / r)²` in microscopy and
  photolithography optical proximity correction can be approximated by sums of `r` real and `c`
  complex-conjugate Gaussians, as in
  [kernel-optimizer](https://github.com/OlliNiemitalo/kernel-optimizer). Here
  `separableRank_radial_eq_iff` shows that `r + 2 c` horizontal–vertical pass pairs (`2 r + 4 c`
  1-D passes) is the exact minimum over `ℝ` for that representation.
* **Isotropic low-pass filtering and steerable edge or orientation analysis.** An ideal 2-D
  circular low-pass filter `ω_c J₁(ω_c r) / (2π r)` removes pixel-grid diagonal bias, has infinite
  separable rank because of its algebraic radial decay, and can be approximated by complex-rate
  Gaussians
  ([DSP Stack Exchange #58449](https://dsp.stackexchange.com/questions/58449/efficient-implementation-of-2-d-circularly-symmetric-low-pass-filter)).
  Applying the `m`-th harmonic ("beach-ball") differential operator
  `((∂_x + i ∂_y) / 2)^m`
  ([Mathematics Stack Exchange #3232122](https://math.stackexchange.com/questions/3232122/beach-ball-like-differential-operators-of-a-two-dimensional-function),
  whose directional-derivative decomposition is the equal-factor case of `re_prod_eq_sum_re`) to
  any smooth radial kernel `φ(x² + y²)` produces the pure polar-separable harmonic
  `(x + i y)^m φ^(m)(x² + y²) = r^m exp(i m θ) φ^(m)(r²)` with no lower-order radial derivative
  terms. When `φ` is a well-formed multi-Gaussian profile with `r` real and `c` nonreal
  upper-half-plane rates (all `λᵢ ≠ 0`), `φ^(m)` is again a well-formed multi-Gaussian profile at
  the same rates (weighted by `λᵢ^m`), so differentiating the continuous-space kernel on `ℝ²`
  analytically before sampling—preserving exact isotropic derivative response up to Nyquist, as in
  [DSP Stack Exchange #58287](https://dsp.stackexchange.com/a/58287/15347)—yields exact
  continuous-domain 2-way real separable ranks `(⌊m / 2⌋ + 1) (r + 2 c)` for the `cos(m θ)`
  kernel and `⌈m / 2⌉ (r + 2 c)` for the `sin(m θ)` kernel (in particular, `r + 2 c` each for the
  `m = 1` gradient pair, with `x` or `y` absorbed directly into one 1-D factor; sampling those
  1-D factors gives at most that many discrete pass pairs).
* **3-D volumetric filtering and band-limited wave propagation (`d = 3`).** In 3-D imaging
  (cryo-EM, CT, MRI) and dispersion-free band-limited acoustic time-stepping—where advancing the
  constant-speed wave equation on a coarse Cartesian grid applies a spherically symmetric radial
  operator—direct `L³` stencils quickly become prohibitive. For `r` real and `c`
  complex-conjugate Gaussians, `separableRank_radial_gaussian_profile` gives exact real 3-way
  rank `r + 3 c`: the alternating root-of-unity identity `re_prod_eq_sum_re` realizes each
  complex-rate Gaussian in `3` real 3-way terms (`9` real 1-D passes on real-valued volume
  buffers, rather than `2^(3 - 1) = 4` terms / `12` passes from naive real-and-imaginary
  expansion), and proves that no real 3-way factorization uses fewer than `r + 3 c` terms.
* **Radial Green's functions and Gaussian-type orbitals.** Representing radial kernels such as
  Coulomb `1 / r`, Yukawa `exp(-κ r) / r`, and oscillatory Helmholtz `exp(i k r) / r` kernels as
  sums of real or complex Gaussians turns non-separable 3-D convolution and multi-center
  integrals into sums of 1-D coordinate products (as in Boys/Gaussian expansions in quantum
  chemistry and separated-representation fast solvers); the classification theorem establishes
  that exponential-polynomial profiles in `r²` are the only continuous radial kernels admitting
  exact finite coordinatewise rank.
* **Ellipsoidal and `ℓ_p` coordinate warps.** Because coordinatewise surjections preserve
  separable rank (`separableRank_comp_surjective`), the same classification and exact rank
  formulas hold verbatim for axis-aligned anisotropic kernels `φ(∑ j, x_j² / a_j²)` (such as
  stretched voxel spacings) and `ℓ_p` superellipsoidal profiles `φ(∑ j, |x_j|^p)` (`p > 0`).

## Files

The proof is in [KernelRankLean](KernelRankLean):

| File | Content |
|---|---|
| `Defs.lean` | Multi-way separable rank, coordinate surjections, 2-D slices, components, `multiTotalCost`, 2-D and Gaussian costs |
| `RowSpan.lean` | Two-coordinate separable rank = dimension of the span of the rows |
| `Complexification.lean` | Scalar extension `ℝ → ℂ` bounds multi-way rank and preserves two-coordinate rank |
| `Translations.lean` | `d`-D radial-to-Hankel equivalence, 2-D slice bound, and `translateSpan` |
| `ExpPoly.lean`, `RealExpPoly.lean` | Uniqueness and conjugation of exponential polynomials |
| `ComplexRank.lean` | Product annihilators; 2-D complex translate-span dimension by Taylor expansion and Cayley–Hamilton |
| `Differential.lean` | Half-line differential operators; Cayley–Hamilton annihilators of exponential orbits |
| `Semigroup.lean` | Continuous one-parameter semigroups in a Banach algebra are `exp (t A)` |
| `TranslationSemigroup.lean` | Shared basis-free exponential realization of translation |
| `Representation.lean` | Regrouping a real exponential-polynomial sum by conjugate pairs |
| `Necessity.lean` | A finite-rank radial kernel's profile is a sum of components |
| `Annihilator.lean` | 2-D rank equals the least constant-coefficient differential-annihilator order |
| `MultiComplexRank.lean` | Exact `d`-way complex exponential-polynomial rank `∑ i, ((d - 1) deg Pᵢ + 1)` |
| `MultiRealRank.lean` | Root-of-unity & real Lagrange decompositions; exact `d`-way real rank `multiTotalCost d cs` |
| `Main.lean` | The `d`-D and 2-D main theorems |

Outside the proof:

| Directory | Content |
|---|---|
| [Experiments](Experiments) | Lean library: alternative proofs of the semigroup step, with their own [README](Experiments/README.md) |
| [Isabelle](Isabelle) | Isabelle/HOL session `KernelRank_NSA`: a nonstandard proof of the semigroup step |
| [paper](paper) | Preprint manuscript (`main.tex`, `main.pdf`, `metadata.json`), published on aiXiv as [`aixiv.261111.000007`](https://aixiv.science/abs/aixiv.261111.000007) |
| [scripts](scripts), [.githooks](.githooks) | Setup, tool wrappers, paper build/submission scripts, and the checks run before each commit |

## Commit history and Lean source size

These counts include **every `.lean` file of the `KernelRankLean` library**, including its root
import module and all helper modules. The separate `Experiments` library (see
[below](#alternative-proofs-of-the-semigroup-step)) is not part of the proof and is counted
separately, in its own README. Physical lines include comments and blank lines;
nonblank lines include comments but exclude whitespace-only lines. Dependencies, build
outputs and external scratch files are excluded. Each committed revision is counted from
its Git contents, not from the current checkout.

Counts use the code as committed: no reformatting, and no removal of comments or blank lines
to improve the totals. Added abstractions count in full:
moving a proof into a helper does not itself reduce the total. Line counts describe source
size, not mathematical complexity.

| Revision | Change | Physical lines | Nonblank lines | Physical-line delta |
|---|---|---:|---:|---:|
| [`2e5ff3f`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/2e5ff3fd937e7bcd4bf1436dca334a77f64fd5ba) | Initial complete separable-rank proof | 1,370 | 1,194 | - |
| [`0d9d939`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/0d9d93961eedd646b689786514d33255fac6c711) | Simplify translation continuity and semigroup smoothing | 1,316 | 1,142 | -54 |
| [`83a404c`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/83a404c7298338065b70fdc39827671a1ec3b695) | Share real/imaginary independence through coefficient synthesis | 1,341 | 1,159 | +25 |
| [`240dea0`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/240dea077b40a8aa9ce0e90ea13d8e546614f594) | Compute exact rank over the complex numbers; use conjugate expansion and scalar extension | 1,340 | 1,169 | -1 |
| [`40bfb90`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/40bfb90deb6a25928f07083cb2085605039dfd24) | Add minimal differential annihilators and share the basis-free translation realization | 1,680 | 1,457 | +340 |
| [`cae13d6`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/cae13d6897f6ce6ef43b86129d938842b0349683) | Use product annihilators and Cayley–Hamilton; delete coefficient-synthesis and cyclic-vector machinery | 1,587 | 1,380 | -93 |
| [`6aabb4d`](https://github.com/OlliNiemitalo/kernel-rank-lean/commit/6aabb4df4788c60673e493bce13662167e599915) | Extend to `d` dimensions (`d ≥ 2`): unified multi-way separability, exact `d`-D complex rank, and exact `d`-D real multi-Gaussian rank | 3,822 | 3,537 | +2,235 |
| This revision | Prove exact `d`-D real radial rank for arbitrary polynomial degrees (`MultiRealRank.lean`), deleting superseded `Sufficiency.lean` and `MultiGaussian.lean` | 5,324 | 5,021 | +1,502 |

Deltas compare consecutive rows (the commits between `cae13d6` and `6aabb4d` only touch
`Experiments` and `Isabelle`). Through `240dea0`, the 2-D proof is **30 physical lines and 25
nonblank lines smaller** than the initial proof. Complexification saved 110 lines in the
proof-specific parts, but its reusable infrastructure makes the whole change essentially
size-neutral: one fewer physical line and ten more nonblank lines.

The `40bfb90` stage is not a like-for-like shortening of the original theorem: it adds
the differential-annihilator characterization. That extension initially brought the total
to 1,726 physical lines; sharing the translation realization then removed 46, yielding
1,680. The intermediate 1,726-line version was not committed. The 1,680-line stage
exceeds `240dea0` by 340 physical lines, with both new modules included.

`cae13d6` removes superseded proof machinery while preserving the classification and
minimal-annihilator statements: **93 fewer physical lines and 77 fewer nonblank lines** than
`40bfb90`, counting the new differential-operator module too.
It still has **271 more physical lines than `0d9d939`** (and 247 more than `240dea0`).
Thus it reduces the extended proof, but has not yet made it smaller than the earlier
classification-only proof.

`6aabb4d` extends `KernelRankLean` from two coordinates to arbitrary dimension `d ≥ 2` for
complex exponential polynomials and real multi-Gaussians (3,822 physical lines, 3,537 nonblank).
This revision replaces both the degree-0-only `MultiGaussian.lean` and `Sufficiency.lean` with
[MultiRealRank.lean](KernelRankLean/MultiRealRank.lean) (2,562 physical lines), proving the
exact `d`-way real radial rank `multiTotalCost d cs` for arbitrary polynomial degrees and all
`d ≥ 2` (`(d - 1) deg P + 1` per real rate and `2 (d - 1) deg P + d` per nonreal rate). This
brings `KernelRankLean` to **5,324 physical lines and 5,021 nonblank lines** (+1,502 physical
lines and +1,484 nonblank lines over `6aabb4d`), completing the unconditional `d`-dimensional
real classification and exact-rank theorem.

## Alternative proofs of the semigroup step

One step of the proof shows that a one-parameter semigroup `M`, with `M (s + t) = M s * M t`
and `M 0 = 1`, that is continuous on `[0, ∞)` is an exponential: `M t = exp (t A)`. Translation
of the profile is such a semigroup, so this step produces the generator `A`.
[Semigroup.lean](KernelRankLean/Semigroup.lean) proves it by smoothing with an integral. It
works in any Banach algebra.

[Experiments](Experiments) and [Isabelle](Isabelle) hold four other proofs of this step, all
complete and all for finite-dimensional algebras. None of them is used by the main proof.
[Experiments/README.md](Experiments/README.md) describes and compares them:

* **Finite differences.** The difference quotients `(M h - 1) / h` are bounded, so a
  subsequence converges to the generator.
* **Nonstandard analysis, after Euler.** Take an infinitesimal step `ε`. The generator is read
  off from the standard part of the change `M ε - 1`, measured on a suitable infinitesimal
  scale, and `⌊t / ε⌋` steps of `M` differ from as many steps of the exponential by an
  infinitesimal. This argument has three formalizations: in Isabelle/HOL with its nonstandard
  analysis library, in Lean with sequences along an ultrafilter, and in Lean in nonstandard
  language on a small interface.

Their sizes, with every helper counted in full:

| Proof of the semigroup step | Physical lines | Nonblank lines |
|---|---:|---:|
| Integral smoothing (used by the main proof) | 96 | 87 |
| Finite differences | 256 | 233 |
| Nonstandard, Lean, with sequences | 206 | 190 |
| Nonstandard, Lean, in nonstandard language (195 of the lines are the interface) | 399 | 344 |
| Nonstandard, Isabelle/HOL | 275 | 253 |

None is shorter than the integral proof, and none is as general, so the main proof keeps it.
The nonstandard argument is more elementary: it uses no integration, and its only estimate is
algebraic.

## Suggested kernel-optimizer citation

The following replacement paragraph cites the verified complex-rank proof at an immutable
revision, rather than whichever proof happens to be on `main`. It does not describe the
additional differential-annihilator characterization.

> *Machine-checked proof.* The theorem is formalized in Lean 4 with Mathlib in
> [kernel-rank-lean at commit `240dea0`](https://github.com/OlliNiemitalo/kernel-rank-lean/tree/240dea077b40a8aa9ce0e90ea13d8e546614f594)
> ([`KernelRank.separableRank_radial_eq_iff`](https://github.com/OlliNiemitalo/kernel-rank-lean/blob/240dea077b40a8aa9ce0e90ea13d8e546614f594/KernelRankLean/Main.lean)),
> with no unproved steps. In step (3), continuity uses the pointwise topology and automatic
> continuity of finite-dimensional linear maps; integral smoothing shows that the translation
> semigroup is $e^{tA}$, and generalized eigenvectors give exponential polynomials. In step (4),
> independent monomial and Hasse-derivative factor families give the exact rank over
> $\mathbb{C}$. Nonreal components are expanded into conjugate pairs, and complexification
> preserves the rank of the real-valued kernel.

That revision uses Lean `v4.36.0-rc2` and Mathlib `v4.36.0-rc2` at commit
`9d581dfff2e41de989072ea63abf3daf69311520`, recorded in its
[dependency manifest](https://github.com/OlliNiemitalo/kernel-rank-lean/blob/240dea077b40a8aa9ce0e90ea13d8e546614f594/lake-manifest.json).

## Building

The build is self-contained on Linux. From the repository root:

```
scripts/setup
scripts/check
```

`scripts/setup` installs [elan](https://github.com/leanprover/elan) (Lean) and
[Isabelle2026](https://isabelle.in.tum.de/) into the ignored `.tmp/` directory, which also holds
the Mathlib cache and all build outputs, and enables the repository's git hooks.

`scripts/check` checks both proofs: the Lean build, that no Lean file uses `sorry`, that the
main theorems and the alternative proofs use only the axioms `propext`,
`Classical.choice` and `Quot.sound`, the Isabelle build, and that the Isabelle theorem uses no
oracle (such as `sorry`) and the theory adds no axioms. It records each passing check in
`.tmp/checks/`, keyed by a hash of the exact input files. The pre-commit hook runs the same
script on the staged files and repeats a check only if its inputs changed since it last passed.

The first check downloads the Mathlib cache and builds Isabelle's `HOL-Analysis` heap, which
took 9 minutes with 4 parallel jobs; after that, a full check takes under a minute.

To run the tools directly, use the wrappers, which use the installation in `.tmp/`:

```
scripts/lake build
scripts/isabelle build -d Isabelle KernelRank_NSA
```

`lake build` builds both the `KernelRankLean` proof and the `Experiments` library.

## License

Released into the public domain under [CC0 1.0 Universal](LICENSE).
