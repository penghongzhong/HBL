import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import HBL.TypeIIDynamicSelection.ActualOriginGreenIntegrable
import Mathlib.Tactic

/-!
# Actual Hartree compatibility transports the singular Green coefficient

The literal normalized Kummer Green field has a potentially singular origin
fundamental solution Y(r) multiplied by the outgoing source integral A(r).
Merely bounding Y and A separately loses a power at the moving left interface.

The genuine two-real-speed compatibility forces the FULL upper-to-lower
source moment A(r0) to equal the original left Fredholm outgoing trace.
Subtracting the actual intervening source integral yields an exact identity
for EVERY point of the moving Kummer annulus. This preserves cancellation
against the source-selected inner jet, and makes the local moment explicit.

No free homogeneous coefficient, prescribed source, or Type-II rate enters.
The quantitative bounds for this transported cancellation and the complete
full-Hartree s^(-9/4) residual still require genuine physical estimates.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Original outgoing Green coefficient at every interior radius equals the
actual selected left Fredholm trace minus the intervening TRUE source moment.
The full original Wronskian density and both interval endpoints are kept. -/
theorem actual_Hartree_compatible_singular_Green_coefficient_local_transport
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume a b)
    (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    originGreenCoeffA K b F r =
      actualOriginOutgoingTrace K a U DU -
        ∫ x in a..r, originGreenSourceA K F x := by
  have hSource :
      originGreenCoeffA K b F a = actualOriginOutgoingTrace K a U DU := by
    have hEq :
        actualOriginOutgoingTrace K a U DU - originGreenCoeffA K b F a = 0 := by
      simpa only [actualMomentLockedIntervalObstruction] using hzero
    exact (sub_eq_zero.mp hEq).symm
  have hInt :=
    (actual_origin_Green_source_integrability K hK hab F hF).1
  have hLeft : IntervalIntegrable (originGreenSourceA K F) volume a r := by
    apply hInt.mono_set
    rw [uIcc_of_le hr.1, uIcc_of_le hab]
    intro x hx
    exact ⟨hx.1, hx.2.trans hr.2⟩
  have hRight : IntervalIntegrable (originGreenSourceA K F) volume r b := by
    apply hInt.mono_set
    rw [uIcc_of_le hr.2, uIcc_of_le hab]
    intro x hx
    exact ⟨hr.1.trans hx.1, hx.2⟩
  have hSplit :=
    intervalIntegral.integral_add_adjacent_intervals hLeft hRight
  calc
    originGreenCoeffA K b F r =
        originGreenCoeffA K b F a -
          ∫ x in a..r, originGreenSourceA K F x := by
      unfold originGreenCoeffA
      linear_combination -hSplit
    _ = actualOriginOutgoingTrace K a U DU -
          ∫ x in a..r, originGreenSourceA K F x := by
      rw [hSource]

/-- Source-dependent full matched physical Kummer field in a form that
exhibits the Cauchy-jet cancellation of the seemingly singular channel.
This is the original full Green field, not just an outer indicator tail. -/
theorem actual_Hartree_compatible_full_Kummer_Green_source_transport
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume a b)
    (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (r : ℝ) (hr : r ∈ Icc a b) :
    actualOriginMatchedKummerValue K a b F U DU r =
      originPhysicalValue K.y r *
        (actualOriginOutgoingTrace K a U DU -
          ∫ x in a..r, originGreenSourceA K F x) +
        originPhysicalValue K.x r *
          (originGreenCoeffB K a F r +
            actualOriginMatchedRegularCoeff K a b F U DU) := by
  have hSing :
      actualOriginMatchedSingularCoeff K a b F U DU = 0 :=
    (actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F U DU).trans
      hzero
  have hTrans :=
    actual_Hartree_compatible_singular_Green_coefficient_local_transport
      K a b C hK hab F hF U DU hzero r hr
  calc
    actualOriginMatchedKummerValue K a b F U DU r =
        originPhysicalValue K.y r * originGreenCoeffA K b F r +
          originPhysicalValue K.x r *
            (originGreenCoeffB K a F r +
              actualOriginMatchedRegularCoeff K a b F U DU) := by
      unfold actualOriginMatchedKummerValue originGreenValue
      rw [hSing]
      ring
    _ = originPhysicalValue K.y r *
          (actualOriginOutgoingTrace K a U DU -
            ∫ x in a..r, originGreenSourceA K F x) +
        originPhysicalValue K.x r *
          (originGreenCoeffB K a F r +
            actualOriginMatchedRegularCoeff K a b F U DU) := by
      rw [hTrans]

end HBL.TypeIIDynamicSelection
