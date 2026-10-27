import HBL.CenterCoercivity
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The actual constrained centre space

The repaired main proof does not evolve an arbitrary energy pair.  It evolves
the common kernel of the three already verified bounded constraints:
scale, phase, and the single negative real direction.  This file constructs
that closed Banach/Hilbert subspace explicitly and transfers the accepted
two-channel coercivity to it.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped RealInnerProductSpace

namespace HBL.MainBackward

open HBL.Modulation
open HBL.Modulation.Monopole

/-- Scale constraint on the real component of the centre pair. -/
def centerScaleFunctional : CenterPair →L[ℝ] ℝ :=
  scaleCompactTest.comp
    (ContinuousLinearMap.fst ℝ FullRadialEnergyL2 FullRadialEnergyL2)

/-- Phase constraint on the imaginary component. -/
def centerPhaseFunctional : CenterPair →L[ℝ] ℝ :=
  phaseCompactTest.comp
    (ContinuousLinearMap.snd ℝ FullRadialEnergyL2 FullRadialEnergyL2)

/-- Orthogonality to the unique negative real direction. -/
def centerNegativeFunctional : CenterPair →L[ℝ] ℝ :=
  (innerSL ℝ fullBubbleRadialEnergyL2).comp
    (ContinuousLinearMap.fst ℝ FullRadialEnergyL2 FullRadialEnergyL2)

/-- The genuine constrained centre subspace used by the repaired backward flow. -/
def constrainedCenterSubmodule : Submodule ℝ CenterPair :=
  centerScaleFunctional.ker ⊓
    centerPhaseFunctional.ker ⊓
      centerNegativeFunctional.ker

abbrev ConstrainedCenterSpace := constrainedCenterSubmodule

theorem mem_constrainedCenterSubmodule_iff (z : CenterPair) :
    z ∈ constrainedCenterSubmodule ↔
      scaleCompactTest z.1 = 0 ∧
      phaseCompactTest z.2 = 0 ∧
      inner ℝ fullBubbleRadialEnergyL2 z.1 = 0 := by
  simp [constrainedCenterSubmodule, centerScaleFunctional,
    centerPhaseFunctional, centerNegativeFunctional, and_assoc]

theorem constrainedCenterSubmodule_isClosed :
    IsClosed (constrainedCenterSubmodule : Set CenterPair) := by
  unfold constrainedCenterSubmodule
  exact (centerScaleFunctional.isClosed_ker.inter
    centerPhaseFunctional.isClosed_ker).inter
      centerNegativeFunctional.isClosed_ker

noncomputable instance constrainedCenterCompleteSpace :
    CompleteSpace ConstrainedCenterSpace :=
  constrainedCenterSubmodule_isClosed.completeSpace_coe

/-- The accepted physical two-channel gap is a genuine coercive estimate on
the actual constrained centre subspace. -/
theorem constrainedCenter_base_coercive
    (z : ConstrainedCenterSpace) :
    compactTwoChannelGap * (‖z.1.1‖ ^ 2 + ‖z.1.2‖ ^ 2) ≤
      centerBaseForm z.1 := by
  have hz := (mem_constrainedCenterSubmodule_iff z.1).1 z.2
  exact actualCompactTwoChannelCoercivity_certified.2.2.2.1
    z.1.1 z.1.2 hz.1 hz.2.1 hz.2.2

/-- The small moving Hessian perturbation preserves a uniform positive gap on
the same constrained subspace. -/
theorem constrainedCenter_moving_coercive
    (K : CenterPair →L[ℝ] CenterPair →L[ℝ] ℝ)
    (hK : ‖K‖ ≤ compactTwoChannelGap / 2)
    (z : ConstrainedCenterSpace) :
    (compactTwoChannelGap / 2) *
        (‖z.1.1‖ ^ 2 + ‖z.1.2‖ ^ 2) ≤
      centerBaseForm z.1 + K z.1 z.1 := by
  have hz := (mem_constrainedCenterSubmodule_iff z.1).1 z.2
  have hgap : 0 < compactTwoChannelGap :=
    actualCompactTwoChannelCoercivity_certified.2.1
  have hpair :
      ‖z.1‖ ^ 2 ≤ ‖z.1.1‖ ^ 2 + ‖z.1.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖z.1.1‖ ‖z.1.2‖ with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ‖z.1.1‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ‖z.1.2‖]
  have hquad0 :
      |K z.1 z.1| ≤ ‖K‖ * ‖z.1‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc
      ‖K z.1 z.1‖ ≤ ‖K z.1‖ * ‖z.1‖ := (K z.1).le_opNorm z.1
      _ ≤ (‖K‖ * ‖z.1‖) * ‖z.1‖ := by
        exact mul_le_mul_of_nonneg_right (K.le_opNorm z.1) (norm_nonneg _)
      _ = ‖K‖ * ‖z.1‖ ^ 2 := by ring
  have hquad :
      |K z.1 z.1| ≤
        (compactTwoChannelGap / 2) *
          (‖z.1.1‖ ^ 2 + ‖z.1.2‖ ^ 2) := by
    calc
      |K z.1 z.1| ≤ ‖K‖ * ‖z.1‖ ^ 2 := hquad0
      _ ≤ (compactTwoChannelGap / 2) * ‖z.1‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hK (sq_nonneg _)
      _ ≤ (compactTwoChannelGap / 2) *
          (‖z.1.1‖ ^ 2 + ‖z.1.2‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hpair (by linarith)
  exact center_coercive_under_small_form_perturbation
    K (compactTwoChannelGap / 2) (by linarith)
    (by linarith) z.1.1 z.1.2 hz.1 hz.2.1 hz.2.2 hquad

#print axioms mem_constrainedCenterSubmodule_iff
#print axioms constrainedCenterSubmodule_isClosed
#print axioms constrainedCenter_base_coercive
#print axioms constrainedCenter_moving_coercive

end HBL.MainBackward
