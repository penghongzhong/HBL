import HBL.TypeIIDynamicSelection.ActualOriginRegularCoefficientTimeDerivative
import HBL.TypeIIDynamicSelection.ActualOriginGreenAffineSourceDerivative
import HBL.TypeIIDynamicSelection.ActualOriginRegularUpperJetTimeDerivative
import Mathlib.Tactic

/-!
# Time derivative of the compatibility-cancelled upper Kummer jet
# for an affine finite-profile source

For the recurrent source class
  F(t,r) = F0(r) + alpha(t) G(r),
the regular scalar coefficient after compatibility cancellation is the sum of
* the forced regular coefficient determined by the moving lower Cauchy jet;
* the regular Green coefficient of the same affine source.

Both derivatives have already been proved from the actual formulas.  This
file only composes them and then differentiates the fixed regular upper basis
jet.  No independent upper-jet differentiability or decay is assumed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualOriginAffineRegularGamma
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (r0 alpha : ℝ → ℝ)
    (F0 G : ℝ → ℂ) (U DU : ℝ → ℂ) (t : ℝ) : ℂ :=
  actualOriginMatchedRegularCoeff K (r0 t) B
      (fun r => F0 r + (alpha t : ℂ) * G r) (U t) (DU t) +
    originGreenCoeffB K (r0 t)
      (fun r => F0 r + (alpha t : ℂ) * G r) B

def actualOriginAffineRegularGammaDot
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (r0 alpha : ℝ → ℝ)
    (F0 G : ℝ → ℂ) (U DU : ℝ → ℂ)
    (s r0dot alphadot : ℝ) (Udot DUdot : ℂ) : ℂ :=
  actualOriginRegularCoeffFromMovingJetDot
      K r0 U DU s r0dot Udot DUdot +
    (r0dot • (-originGreenSourceB K F0 (r0 s)) +
      ((alphadot : ℂ) * originGreenCoeffB K (r0 s) G B +
        (alpha s : ℂ) *
          (r0dot • (-originGreenSourceB K G (r0 s)))))

theorem actual_origin_affine_regular_gamma_hasDerivAt
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (B : ℝ) (hK : OriginBasisOn K lo hi C)
    (hloB : lo < B) (hBhi : B ≤ hi)
    (F0 G : ℝ → ℂ) (hF0 : Continuous F0) (hG : Continuous G)
    (r0 alpha : ℝ → ℝ) (U DU : ℝ → ℂ)
    (s r0dot alphadot : ℝ) (Udot DUdot : ℂ)
    (hr : r0 s ∈ Ioo lo B)
    (hr0 : HasDerivAt r0 r0dot s)
    (halpha : HasDerivAt alpha alphadot s)
    (hU : HasDerivAt U Udot s)
    (hDU : HasDerivAt DU DUdot s) :
    HasDerivAt
      (actualOriginAffineRegularGamma K B r0 alpha F0 G U DU)
      (actualOriginAffineRegularGammaDot
        K B r0 alpha F0 G U DU s r0dot alphadot Udot DUdot) s := by
  have hrHi : r0 s ∈ Ioo lo hi :=
    ⟨hr.1, hr.2.trans_le hBhi⟩
  have hReg :=
    actual_origin_matched_regular_coeff_moving_hasDerivAt
      K C B hK r0 (fun t r => F0 r + (alpha t : ℂ) * G r) U DU
      s r0dot Udot DUdot hrHi hr0 hU hDU
  have hKB : OriginBasisOn K lo B C := by
    intro r hrB
    exact hK r ⟨hrB.1, hrB.2.trans hBhi⟩
  have hGreen :=
    actual_origin_Green_coeffB_moving_affine_source_hasDerivAt
      (hi := B) K hKB hloB F0 G hF0 hG r0 alpha s r0dot alphadot
      hr hr0 halpha
  have hsum := hReg.add hGreen
  simpa only [actualOriginAffineRegularGamma,
    actualOriginAffineRegularGammaDot] using hsum

/-- The actual upper value and slope have the same scalar derivative.
The singular mode is absent because this theorem is only for the
compatibility-cancelled regular channel. -/
theorem actual_origin_affine_regular_upper_jet_hasDerivAt
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (B : ℝ) (hK : OriginBasisOn K lo hi C)
    (hloB : lo < B) (hBhi : B ≤ hi)
    (F0 G : ℝ → ℂ) (hF0 : Continuous F0) (hG : Continuous G)
    (r0 alpha : ℝ → ℝ) (U DU : ℝ → ℂ)
    (s r0dot alphadot : ℝ) (Udot DUdot : ℂ)
    (hr : r0 s ∈ Ioo lo B)
    (hr0 : HasDerivAt r0 r0dot s)
    (halpha : HasDerivAt alpha alphadot s)
    (hU : HasDerivAt U Udot s)
    (hDU : HasDerivAt DU DUdot s) :
    let gamma :=
      actualOriginAffineRegularGamma K B r0 alpha F0 G U DU
    let gammaDot :=
      actualOriginAffineRegularGammaDot
        K B r0 alpha F0 G U DU s r0dot alphadot Udot DUdot
    HasDerivAt (actualOriginRegularUpperValue K B gamma)
      (originPhysicalValue K.x B * gammaDot) s ∧
    HasDerivAt (actualOriginRegularUpperSlope K B gamma)
      (originPhysicalSlope K.x K.dx B * gammaDot) s := by
  dsimp only
  let gamma :=
    actualOriginAffineRegularGamma K B r0 alpha F0 G U DU
  let gammaDot :=
    actualOriginAffineRegularGammaDot
      K B r0 alpha F0 G U DU s r0dot alphadot Udot DUdot
  have hGamma : HasDerivAt gamma gammaDot s := by
    dsimp [gamma, gammaDot]
    exact actual_origin_affine_regular_gamma_hasDerivAt
      K B hK hloB hBhi F0 G hF0 hG r0 alpha U DU
      s r0dot alphadot Udot DUdot hr hr0 halpha hU hDU
  exact actual_origin_regular_upper_jet_hasDerivAt
    K B gamma s gammaDot hGamma

end HBL.TypeIIDynamicSelection
