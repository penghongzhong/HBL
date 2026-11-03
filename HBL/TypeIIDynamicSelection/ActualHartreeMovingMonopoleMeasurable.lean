import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleRadialDecay
import HBL.MonopoleProfileEquation
import Mathlib.Tactic

/-!
# Actual moving monopole measurability on the whole real radius

The physical monopole radius R(c)=4/|c| is totalized at c=0.
Use its exact cutoff identity instead of an unproved guessed
'monopoleMovingCutoffProfile_measurable.comp' syntax.
The normalized profile is the continuous bubble plus a measurable
radial Fredholm profile divided by the (totalized) real radius.
No new analytic Hartree assumption or axiom is required.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- True amplitude-dependent Hartree monopole profile is measurable,
including the physical origin and the c=0 transition. -/
theorem actual_Hartree_moving_monopole_measurable (c : ℝ) :
    Measurable
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) := by
  have hRadial : Measurable monopoleRadialProfile := by
    unfold monopoleRadialProfile
    exact monopoleProfile_continuous.measurable.div measurable_id
  have hCut : Measurable (fun r : ℝ =>
      cutoff (|c| * r / 4)) := by
    have hArg : Continuous (fun r : ℝ => |c| * r / 4) :=
      (continuous_const.mul continuous_id).div_const 4
    exact (cutoff_contDiff_infty.continuous.comp hArg).measurable
  have hBubble : Measurable bubble :=
    bubble_contDiff_infty.continuous.measurable
  have hFull : Measurable (fun r : ℝ =>
      bubble r + c * (1 - cutoff (|c| * r / 4)) *
        monopoleRadialProfile r) := by
    exact hBubble.add
      ((measurable_const.mul (measurable_const.sub hCut)).mul hRadial)
  have hEq :
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c =
        (fun r : ℝ =>
          bubble r + c * (1 - cutoff (|c| * r / 4)) *
            monopoleRadialProfile r) := by
    funext r
    exact monopoleMovingCutoffProfile_eq c r
  rw [hEq]
  exact hFull

end HBL.TypeIIDynamicSelection
