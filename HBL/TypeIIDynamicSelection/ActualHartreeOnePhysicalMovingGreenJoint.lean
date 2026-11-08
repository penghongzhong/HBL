import HBL.TypeIIDynamicSelection.ActualHartreeMovingGreenJointDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeSlowInnerMovingGreenEndpoint
import Mathlib.Tactic

/-!
# ONE physical quartic Hartree source, ONE moving matching radius,
# ONE original Kummer Green joint time derivative

The source is the genuine nonlocal quartic Hartree Riesz forcing
with a unique real two-channel Cramer correction, not independent
data.  The matching radius is r0(s)=ell(s)^(-1/16)/a(s), not a free
differentiable endpoint. Its derivative comes from the physical
parameter path and does not prescribe a Type-II rate.

The genuine physical source's temporal Green derivative is supplied
through the already strictly verified parametric-integral producer.
This theorem derives the endpoint contribution and proves the mixed
cross term vanishes, provided the original Wronskian-density temporal
Lipschitz and integrability hypotheses hold on the moving sliver.

The spatial Kummer fundamental pair is kept frozen here; its
parameter time derivative and the O(s^(-9/4)) full nonlinear
four-piece Hartree residual remain separate mathematical obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualHartreeOnePhysicalMovingGreenSource
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t

def actualHartreeOnePhysicalMovingGreenLower
    (ell a : ℝ → ℝ) : ℝ → ℝ :=
  fun t => actualHartreeSlowInnerRadius (ell t) / a t

theorem actual_Hartree_one_physical_selected_Green_joint_time_derivative
    {mu theta scale lo hi basisBound : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hBasis : OriginBasisOn K lo hi basisBound)
    (hlohi : lo < hi)
    (ell a c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s ellDot aDot C : ℝ)
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
    (hLip : ∀ t ∈ T,
      ∀ x ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
      ‖originGreenSourceB K
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) x -
        originGreenSourceB K
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s) x‖ ≤
          C * |t-s|)
    (dSource : ℂ)
    (hSource : HasDerivAt
      (fun t => originGreenCoeffB K
        (actualHartreeOnePhysicalMovingGreenLower ell a s)
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) hi)
      dSource s) :
    HasDerivAt
      (fun t => originGreenCoeffB K
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) hi)
      (dSource +
        (((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
           ellDot * a s -
          actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2) •
          (-originGreenSourceB K
            (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s)
            (actualHartreeOnePhysicalMovingGreenLower ell a s))) s := by
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
  have hEnd :=
    actual_Hartree_true_source_slow_inner_moving_Green_endpoint
      K hBasis hlohi ell a c z b w Z s ellDot aDot
      hEll hA hEllPos ha hr0 hFcont
  have hJoint :=
    actual_origin_Green_moving_selected_joint_hasDerivAt
      K F r0 s hi C rDot T hT hR hInt hLip dSource _ hSource hEnd
  exact hJoint

end HBL.TypeIIDynamicSelection
