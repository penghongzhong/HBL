import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterraSlope
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import Mathlib.Tactic

/-!
# Exact full matched Kummer slope from its zero-left Volterra component

The exact original Cramer compatibility condition does not set the full
outgoing Green coefficient to zero at the left interface. Rather, its
left value is the genuine Fredholm outgoing jet trace.

The COMPLETE matched Kummer slope is therefore the zero-left-jet
Volterra slope plus exactly TWO homogeneous contributions:
  (i) the original Fredholm outgoing Wronskian trace times the singular
      origin mode derivative;
  (ii) the uniquely determined regular Cramer coefficient times the
      regular origin mode derivative.

The first coefficient is NOT a freely chosen monopole amplitude.
This identity holds for arbitrary integrable physical sources
and assumes no time exponent, source order or Type-II blowup rate.
The subsequent estimate must pair the original Fredholm trace O(a)
with the singular derivative O(r^-2) before taking the radial energy.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The true matched profile differs from its zero-left source response
by precisely the outgoing *physical left jet* and regular Cramer mode.
It is false to omit the first contribution just because compatibility
has removed the *separate homogeneous* singular coefficient. -/
theorem actual_Hartree_matched_slope_zero_left_plus_original_jet_exact
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ) (hab : a ≤ b)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (U DU : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) :
    (r : ℂ) * actualOriginMatchedKummerSlope K a b F U DU r =
      (r : ℂ) * actualOriginMatchedKummerSlope K a b F 0 0 r +
      (r : ℂ) * (actualOriginOutgoingTrace K a U DU *
        originPhysicalSlope K.y K.dy r) +
      (r : ℂ) * (actualOriginMatchedRegularCoeff K a b F U DU *
        originPhysicalSlope K.x K.dx r) := by
  have hFullSing :
      actualOriginMatchedSingularCoeff K a b F U DU = 0 :=
    (actual_origin_matched_Kummer_singular_eq_obstruction
      K hK hab F U DU).trans hCompatible
  have hZeroSing :
      actualOriginMatchedSingularCoeff K a b F 0 0 =
        -originGreenCoeffA K b F a := by
    rw [actual_origin_matched_Kummer_singular_eq_obstruction
      K hK hab F 0 0]
    unfold actualMomentLockedIntervalObstruction actualOriginOutgoingTrace
    simp
  have hZeroRegular :
      actualOriginMatchedRegularCoeff K a b F 0 0 = 0 := by
    rw [actual_origin_matched_Kummer_regular_coefficient K a b F 0 0]
    simp
  have hTrace :
      originGreenCoeffA K b F a = actualOriginOutgoingTrace K a U DU := by
    have hEq :
        actualOriginOutgoingTrace K a U DU -
          originGreenCoeffA K b F a = 0 := by
      simpa only [actualMomentLockedIntervalObstruction] using hCompatible
    exact (sub_eq_zero.mp hEq).symm
  unfold actualOriginMatchedKummerSlope
  rw [hFullSing, hZeroSing, hZeroRegular, hTrace]
  ring

end HBL.TypeIIDynamicSelection
