import HBL.TypeIIDynamicSelection.ActualOriginRegularCoefficientTimeDerivative
import HBL.TypeIIDynamicSelection.ActualOriginRegularUpperJetTimeDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeMovingGreenJointDerivative
import Mathlib.Tactic

/-!
# Source-selected Hartree matched regular upper Kummer jet, complete time derivative

The TRUE compatibility-cancelled upper Kummer jet has one forced
regular coefficient
  gamma(t) = beta_reg[U(t),DU(t),r0(t)] + B_K[F(t)](r0(t),B).
No free homogeneous coefficient is added. The first component
beta_reg has the original moving Fredholm left-jet derivative.
The second component has the rigorously established JOINT original
source/endpoint derivative, including its proven vanishing mixed term.

This module composes them for the SAME physical Kummer pair, the SAME
moving left interface and one genuine adjusted source. It then
derives time derivatives of BOTH actual regular upper Kummer value
and slope from the original regular fundamental pair.

The source/endpoint joint derivative is an explicit certificate
supplied by the previous strict theorem, not postulated as a small
remainder. The physical Riesz source and unique Cramer selector will
be instantiated in the next source-specific wrapper.
The spatial Kummer basis is held fixed, and full O(s^-9/4)
original PDE residual remains open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualOriginMovingMatchedRegularGamma
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (r0 : ℝ → ℝ) (F : ℝ → ℝ → ℂ)
    (U DU : ℝ → ℂ) (t : ℝ) : ℂ :=
  actualOriginMatchedRegularCoeff K (r0 t) B (F t) (U t) (DU t) +
    originGreenCoeffB K (r0 t) (F t) B

/-- Both upper regular Kummer boundary derivatives follow from the
same moving physical Fredholm jet and its one joint Green coefficient.
No independent derivative of the completed gamma is assumed. -/
theorem actual_Hartree_moving_matched_regular_upper_jet_hasDerivAt
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (B : ℝ) (hK : OriginBasisOn K lo hi C)
    (r0 : ℝ → ℝ) (F : ℝ → ℝ → ℂ)
    (U DU : ℝ → ℂ)
    (s rdot : ℝ) (Udot DUdot GreenDot : ℂ)
    (hr : r0 s ∈ Ioo lo hi)
    (hR : HasDerivAt r0 rdot s)
    (hU : HasDerivAt U Udot s)
    (hDU : HasDerivAt DU DUdot s)
    (hGreen : HasDerivAt
      (fun t => originGreenCoeffB K (r0 t) (F t) B) GreenDot s) :
    let gamma : ℝ → ℂ :=
      actualOriginMovingMatchedRegularGamma K B r0 F U DU
    let gammaDot : ℂ :=
      actualOriginRegularCoeffFromMovingJetDot
        K r0 U DU s rdot Udot DUdot + GreenDot
    HasDerivAt gamma gammaDot s ∧
    HasDerivAt
      (actualOriginRegularUpperValue K B gamma)
      (originPhysicalValue K.x B * gammaDot) s ∧
    HasDerivAt
      (actualOriginRegularUpperSlope K B gamma)
      (originPhysicalSlope K.x K.dx B * gammaDot) s := by
  have hReg :=
    actual_origin_matched_regular_coeff_moving_hasDerivAt
      K C B hK r0 F U DU s rdot Udot DUdot hr hR hU hDU
  have hGamma :
      HasDerivAt (actualOriginMovingMatchedRegularGamma K B r0 F U DU)
        (actualOriginRegularCoeffFromMovingJetDot
          K r0 U DU s rdot Udot DUdot + GreenDot) s := by
    simpa only [actualOriginMovingMatchedRegularGamma, Pi.add_apply] using
      hReg.add hGreen
  have hUpper :=
    actual_origin_regular_upper_jet_hasDerivAt
      K B (actualOriginMovingMatchedRegularGamma K B r0 F U DU)
      s _ hGamma
  exact ⟨hGamma, hUpper.1, hUpper.2⟩

end HBL.TypeIIDynamicSelection
