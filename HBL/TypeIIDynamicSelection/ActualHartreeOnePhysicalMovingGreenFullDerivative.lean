import HBL.TypeIIDynamicSelection.ActualHartreeOnePhysicalMovingGreenJoint
import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingSelectedRegularGreenDerivative
import Mathlib.Tactic

/-!
# One original Hartree source with both moving Green derivatives

This connects the genuine Cramer-selected nonlocal Hartree source derivative
and the original slow-inner moving endpoint. The fixed-endpoint source
derivative is now a theorem output, rather than an independent hypothesis.
The time-Lipschitz bound on the moving sliver and integrable derivative
majorants are explicitly assumed; no full-PDE decay or blowup rate follows.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_one_physical_selected_Green_joint_derivative_from_original_sources
    {mu theta scale lo hi basisBound : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hBasis : OriginBasisOn K lo hi basisBound)
    (hlohi : lo < hi) (hHi : 0 < hi)
    (ell a c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z bdot wdot Zdot : ℝ → ℂ)
    (Fdot Sdot Pdot : ℝ → ℝ → ℂ)
    (s ellDot aDot C : ℝ)
    (T : Set ℝ) (bound : ℝ → ℝ) (hT : T ∈ 𝓝 s)
    (hEll : HasDerivAt ell ellDot s)
    (hA : HasDerivAt a aDot s)
    (hEllPos : 0 < ell s) (ha : 0 < a s)
    (hr0 : actualHartreeOnePhysicalMovingGreenLower ell a s ∈ Ioo lo hi)
    (hFcont : Continuous
      (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s))
    (haT : ∀ t ∈ T, 0 < a t)
    (hb : ∀ t ∈ T, HasDerivAt b (bdot t) t)
    (hw : ∀ t ∈ T, HasDerivAt w (wdot t) t)
    (hZ : ∀ t ∈ T, HasDerivAt Z (Zdot t) t)
    (hColumns : ∀ t ∈ T,
      ‖b t‖ ≤ a t * hi ^ 2 ∧ ‖w t‖ ≤ a t * hi ^ 2)
    (hDet : ∀ t ∈ T,
      (a t) ^ 2 * hi ^ 4 / 256 ≤ actualRealCramerDet (b t) (w t))
    (hPhysicalDeriv : ∀ᵐ r ∂volume,
      r ∈ Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi →
      ∀ t ∈ T,
        HasDerivAt
          (fun u => -actualHartreeLaplacianScaledKummerSource
            (a u) (ell u) (c u) (z u) r) (Fdot t r) t ∧
        HasDerivAt
          (fun u => actualMomentLockedScaledScaleSource (a u) (c u) r)
            (Sdot t r) t ∧
        HasDerivAt
          (fun u => actualMomentLockedScaledPhaseSource (a u) (c u) r)
            (Pdot t r) t)
    (hMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
        (volume.restrict
          (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hSourceInt : IntervalIntegrable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hDotMeas : AEStronglyMeasurable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s))
      (volume.restrict
        (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hBound : ∀ᵐ r ∂volume,
      r ∈ Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi →
      ∀ t ∈ T,
        ‖originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSourceDot
            a ell c z b w Z Fdot Sdot Pdot t) r‖ ≤ bound r)
    (hBoundInt : IntervalIntegrable bound volume
      (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hMovingInt : ∀ t ∈ T,
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
          C * |t-s|) :
    HasDerivAt
      (fun t => originGreenCoeffB K
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) hi)
      (originGreenCoeffB K
        (actualHartreeOnePhysicalMovingGreenLower ell a s)
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s) hi +
        (((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
           ellDot * a s -
          actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2) •
          (-originGreenSourceB K
            (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s)
            (actualHartreeOnePhysicalMovingGreenLower ell a s))) s := by
  have hSource :=
    actual_Hartree_true_moving_selected_regular_Green_hasDerivAt
      K (actualHartreeOnePhysicalMovingGreenLower ell a s) hi s
      a ell c z b w Z bdot wdot Zdot Fdot Sdot Pdot
      T bound hT hHi haT hb hw hZ hColumns hDet
      hPhysicalDeriv hMeas hSourceInt hDotMeas hBound hBoundInt
  exact actual_Hartree_one_physical_selected_Green_joint_time_derivative
    K hBasis hlohi ell a c z b w Z s ellDot aDot C
    T hT hEll hA hEllPos ha hr0 hFcont
    hMovingInt hLip _ hSource

end HBL.TypeIIDynamicSelection
