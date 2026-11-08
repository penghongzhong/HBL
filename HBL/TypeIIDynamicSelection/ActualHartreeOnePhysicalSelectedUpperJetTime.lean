import HBL.TypeIIDynamicSelection.ActualHartreeMovingMatchedRegularUpperJet
import HBL.TypeIIDynamicSelection.ActualHartreeOnePhysicalGreenJointFromDerivative
import Mathlib.Tactic

/-!
# One original Hartree Riesz source: actual complete matched upper Kummer
# regular value and slope have the same derived time derivative

The source is the genuine nonlocal quartic Hartree interaction corrected
by the UNIQUE real two-channel Cramer speed. The moving left radius
is the actual ell(s)^(-1/16)/a(s) matching interface; no Type-II rate
is imposed. The original-source time variation and endpoint motion
are combined by the earlier strictly verified joint Green theorem,
including the quantitative mixed-error cancellation.

The original matched regular homogeneous coefficient is DERIVED from
the moving Fredholm left value/slope. Its time derivative and the
joint selected original Green time derivative are combined to yield
both regular upper Kummer value and slope derivatives.

The actual original source differentiability, time-derivative envelope,
dominated Green source derivative and inner Fredholm jet differentiability
remain explicitly visible analytic inputs. The varying Kummer fundamental
basis and full O(s^(-9/4)) 3D Hartree PDE residual are not proved here.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_one_physical_selected_moving_upper_regular_jet_derivative
    {mu theta scale lo hi basisBound : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hBasis : OriginBasisOn K lo hi basisBound)
    (hlohi : lo < hi)
    (ell a c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s ellDot aDot CK D : ℝ)
    (T : Set ℝ) (hT : T ∈ 𝓝 s)
    (hEll : HasDerivAt ell ellDot s)
    (hA : HasDerivAt a aDot s)
    (hEllPos : 0 < ell s) (ha : 0 < a s)
    (hr0 : actualHartreeOnePhysicalMovingGreenLower ell a s ∈ Ioo lo hi)
    (hFcont : Continuous
      (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s))
    (hInt : ∀ t ∈ T,
      IntervalIntegrable
        (originGreenSourceB K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t))
        volume
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s) ∧
      IntervalIntegrable
        (originGreenSourceB K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t))
        volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi ∧
      IntervalIntegrable
        (originGreenSourceB K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s))
        volume
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s) ∧
      IntervalIntegrable
        (originGreenSourceB K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s))
        volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hRatio : ∀ t ∈ T,
      ∀ r ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
      ‖originPhysicalValue K.y r / originGreenWronskian K r‖ ≤ CK)
    (hPhysicalTimeDerivative : ∀ t ∈ T,
      ∀ r ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
      ∀ τ ∈ Icc (min s t) (max s t),
        ∃ d : ℂ,
          HasDerivAt
            (fun u => actualHartreeTrueMovingAdjustedSource
              a ell c z b w Z u r) d τ ∧
          ‖d‖ ≤ D)
    (U DU : ℝ → ℂ) (Udot DUdot dSource : ℂ)
    (hU : HasDerivAt U Udot s)
    (hDU : HasDerivAt DU DUdot s)
    (hSource : HasDerivAt
      (fun t => originGreenCoeffB K
        (actualHartreeOnePhysicalMovingGreenLower ell a s)
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) hi)
      dSource s) :
    let r0 : ℝ → ℝ := actualHartreeOnePhysicalMovingGreenLower ell a
    let F : ℝ → ℝ → ℂ :=
      actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z
    let rDot : ℝ :=
      ((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
        ellDot * a s -
        actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2
    let gamma : ℝ → ℂ :=
      actualOriginMovingMatchedRegularGamma K hi r0 F U DU
    let gammaDot : ℂ :=
      actualOriginRegularCoeffFromMovingJetDot
        K r0 U DU s rDot Udot DUdot +
      (dSource + rDot • (-originGreenSourceB K (F s) (r0 s)))
    HasDerivAt gamma gammaDot s ∧
    HasDerivAt
      (actualOriginRegularUpperValue K hi gamma)
      (originPhysicalValue K.x hi * gammaDot) s ∧
    HasDerivAt
      (actualOriginRegularUpperSlope K hi gamma)
      (originPhysicalSlope K.x K.dx hi * gammaDot) s := by
  let F : ℝ → ℝ → ℂ :=
    actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z
  let r0 : ℝ → ℝ := actualHartreeOnePhysicalMovingGreenLower ell a
  let rDot : ℝ :=
    ((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
      ellDot * a s -
      actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2
  have hR : HasDerivAt r0 rDot s :=
    actual_Hartree_slow_inner_Kummer_endpoint_time_derivative
      ell a s ellDot aDot hEll hA hEllPos ha
  have hGreen :=
    actual_Hartree_one_physical_Green_joint_from_source_derivative
      K hBasis hlohi ell a c z b w Z
      s ellDot aDot CK D T hT hEll hA hEllPos ha hr0
      hFcont hInt hRatio hPhysicalTimeDerivative dSource hSource
  have hJet :=
    actual_Hartree_moving_matched_regular_upper_jet_hasDerivAt
      K hi hBasis r0 F U DU s rDot Udot DUdot
      (dSource + rDot • (-originGreenSourceB K (F s) (r0 s)))
      hr0 hR hU hDU hGreen
  exact hJet

end HBL.TypeIIDynamicSelection
