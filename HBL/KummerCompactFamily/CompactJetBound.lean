import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem compact_operator_parameter_jets_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) (S : (ℝ × ℝ) → E)
    (hS : ∀ p ∈ A, ContDiffAt ℝ ω S p) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ A, ‖iteratedFDeriv ℝ n S p‖ ≤ C := by
  intro n
  have hc : ContinuousOn (iteratedFDeriv ℝ n S) A := fun p hp =>
    ((hS p hp).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hA.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro p hp
  exact (hC p hp).trans (le_max_left _ _)
end HBL.Profile.Kummer
