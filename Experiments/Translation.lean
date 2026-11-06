import Experiments.FiniteDifferenceSemigroup
import Experiments.NonstandardSemigroup
import KernelRankLean.TranslationSemigroup

/-!
# Both alternative proofs apply to the translation semigroup

`KernelRank.exists_translation_generator` obtains the generator of translation on a
finite-dimensional complex translate space from `KernelRank.exists_eq_exp_of_semigroup`.
Either alternative proof of the semigroup theorem gives the same conclusion.
-/

namespace Experiments

open KernelRank

attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace

theorem exists_translation_generator_finiteDifference (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ a : translateSpan ψ →L[ℂ] translateSpan ψ,
      ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • a) := by
  let : NormedAlgebra ℝ (translateSpan ψ →L[ℂ] translateSpan ψ) := .restrictScalars ℝ ℂ _
  obtain ⟨a, ha⟩ := exists_eq_exp_of_semigroup_finiteDifference (shiftCLM ψ)
    (continuous_shiftCLM ψ hψ).continuousOn (shiftCLM_zero ψ)
    fun s t hs ht => shiftCLM_add ψ hs ht
  exact ⟨a, ha⟩

theorem exists_translation_generator_nonstandard (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ a : translateSpan ψ →L[ℂ] translateSpan ψ,
      ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • a) := by
  let : NormedAlgebra ℝ (translateSpan ψ →L[ℂ] translateSpan ψ) := .restrictScalars ℝ ℂ _
  obtain ⟨a, ha⟩ := exists_eq_exp_of_semigroup_nonstandard (shiftCLM ψ)
    (continuous_shiftCLM ψ hψ).continuousOn (shiftCLM_zero ψ)
    fun s t hs ht => shiftCLM_add ψ hs ht
  exact ⟨a, ha⟩

end Experiments
