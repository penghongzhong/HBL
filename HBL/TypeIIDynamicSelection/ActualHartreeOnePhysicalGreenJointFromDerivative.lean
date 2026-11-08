import HBL.TypeIIDynamicSelection.ActualHartreeOnePhysicalMovingGreenJoint
import HBL.TypeIIDynamicSelection.ActualHartreeSelectedGreenDensityTimeMVT
import Mathlib.Tactic

/-!
# One true quartic Hartree source: joint moving Green derivative from physical time bounds

The previous theorem needed an O(|t-s|) Lipschitz bound for the original
Wronskian density in the short moving matching interval. This file DERIVES
that Lipschitz input from the quantitative time derivative of the SAME
original Riesz/Cramer selected Hartree source and a genuine fixed-Kummer
Wronskian multiplier budget, using Mathlib's mean value theorem.

Thus NO independent time-Lipschitz estimate on the Green density remains.
Original source temporal differentiability and boundedness along a compact
time segment are the explicit physical inputs, not disguised as a source
packet. The real matching radius r0(s)=ell(s)^(-1/16)/a(s) and its derivative
are already produced by the physical-scale theorem, without an assumed
Type-II rate.

The moving Kummer basis and full PDE weighted s^(-9/4) residual are not
consequences of this local-in-time Green theorem.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_one_physical_Green_joint_from_source_derivative
    {mu theta scale lo hi basisBound : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hBasis : OriginBasisOn K lo hi basisBound)
    (hlohi : lo < hi)
    (ell a c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ)
    (s ellDot aDot CK D : ℝ)
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
  have hPhysicalDensityLip : ∀ t ∈ T,
      ∀ r ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
        ‖originGreenSourceB K
            (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) r -
          originGreenSourceB K
            (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s) r‖ ≤
          (CK * D) * |t-s| := by
    intro t ht r hr
    exact actual_Hartree_true_selected_Green_density_time_MVT
      K a ell c z b w Z s t r CK D
      (hRatio t ht r hr)
      (hPhysicalTimeDerivative t ht r hr)
  exact actual_Hartree_one_physical_selected_Green_joint_time_derivative
    K hBasis hlohi ell a c z b w Z s ellDot aDot (CK * D)
    T hT hEll hA hEllPos ha hr0 hFcont
    hInt hPhysicalDensityLip dSource hSource

end HBL.TypeIIDynamicSelection
