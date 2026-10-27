import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# C1 dependence of a uniformly contracting fixed point

This is a generic Banach-space calculus lemma used in the final HBL shooting
graph.  The only input is the standard C1 regularity of the joint map and
the strict contraction bound in the state variable.
-/

noncomputable section
set_option autoImplicit false

open scoped Topology ContDiff

namespace HBL.MainBackward

/-- A state derivative of norm < 1 makes I-D invertible. -/
theorem id_sub_isInvertible_of_norm_lt_one
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (D : X →L[ℝ] X) (hD : ‖D‖ < 1) :
    (ContinuousLinearMap.id ℝ X - D).IsInvertible := by
  have hu : IsUnit (1 - D) := isUnit_one_sub_of_norm_lt_one hD
  rcases hu with ⟨u, hu⟩
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ((↑(u⁻¹) : X →L[ℝ] X)))
  · ext x
    change ((1 - D) * (↑(u⁻¹) : X →L[ℝ] X)) x = x
    rw [← hu]
    simp
  · ext x
    change ((↑(u⁻¹) : X →L[ℝ] X) * (1 - D)) x = x
    rw [← hu]
    simp

/-- Local C1 implicit graph for a fixed-point equation, once the state
partial derivative is identified with I-D and ‖D‖<1. -/
theorem contracting_fixed_point_has_C1_local_graph
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : P × X → X) (p : P) (x : X)
    (D : X →L[ℝ] X)
    (hF : ContDiffAt ℝ 1 F (p,x))
    (hpartial :
      fderiv ℝ F (p,x) ∘L ContinuousLinearMap.inr ℝ P X =
        ContinuousLinearMap.id ℝ X - D)
    (hD : ‖D‖ < 1) :
    ∃ psi : P → X,
      psi p = x ∧
      ContDiffAt ℝ 1 psi p ∧
      ∀ᶠ y in 𝓝 p, F (y, psi y) = F (p,x) := by
  have hinv :
      (fderiv ℝ F (p,x) ∘L ContinuousLinearMap.inr ℝ P X).IsInvertible := by
    rw [hpartial]
    exact id_sub_isInvertible_of_norm_lt_one D hD
  let psi := hF.implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv
  refine ⟨psi, ?_, ?_, ?_⟩
  · exact hF.implicitFunction_apply_self (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv
  · exact hF.contDiffAt_implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv
  · exact hF.eventually_apply_implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv

#print axioms id_sub_isInvertible_of_norm_lt_one
#print axioms contracting_fixed_point_has_C1_local_graph

end HBL.MainBackward
