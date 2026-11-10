import HBL.TypeIIDynamicSelection.ActualHartreeBothGreenTimeRatiosNoLeftLoss
import HBL.TypeIIDynamicSelection.ActualHartreeOnePhysicalMovingSingularGreenFullDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeOnePhysicalMovingGreenFullDerivative
import Mathlib.Tactic

/-!
# Two original Green time derivatives from ONE true Hartree nonlocal source

Both the exact original singular outgoing moment A(r0(s)) and the regular
upper moment B(r0(s)) use the same quartic Riesz interaction and same
explicit Cramer-selected real speeds. Both include the moving original
left endpoint and true source-time derivatives. Crucially their original
Wronskian ratios now follow from the bounded origin-regularized Kummer
modes with a shared coefficient G*hi; no separate radius-dependent
multiplier norm or postulated asymptotic positive time order is used.

Original source differentiability, three Riesz time-velocity dominating
integrals, real Cramer-column bounds, and actual spatial Kummer mode
bounds remain explicit. This is a frozen-basis component of the full
four-region physical PDE, not a Type-II blowup construction.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology Interval
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_one_physical_true_source_both_moving_Green_time_derivatives_no_radius_loss
    {mu theta scale lo hi basisBound : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hBasis : OriginBasisOn K lo hi basisBound)
    (hlohi : lo < hi) (hHi : 0 < hi)
    (ell a c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z bdot wdot Zdot : ℝ → ℂ)
    (Fdot Sdot Pdot : ℝ → ℝ → ℂ)
    (s ellDot aDot G D : ℝ)
    (T : Set ℝ) (boundA boundB : ℝ → ℝ) (hT : T ∈ 𝓝 s)
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
    (hMeasA : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
        (volume.restrict
          (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hSourceIntA : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hDotMeasA : AEStronglyMeasurable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s))
      (volume.restrict
        (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hBoundA : ∀ᵐ r ∂volume,
      r ∈ Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi →
      ∀ t ∈ T,
        ‖originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSourceDot
            a ell c z b w Z Fdot Sdot Pdot t) r‖ ≤ boundA r)
    (hBoundIntA : IntervalIntegrable boundA volume
      (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hMovingIntA : ∀ t ∈ T,
      IntervalIntegrable
        (originGreenSourceA K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t))
        volume
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s) ∧
      IntervalIntegrable
        (originGreenSourceA K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t))
        volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi ∧
      IntervalIntegrable
        (originGreenSourceA K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s))
        volume
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s) ∧
      IntervalIntegrable
        (originGreenSourceA K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s))
        volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hMeasB : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
        (volume.restrict
          (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hSourceIntB : IntervalIntegrable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hDotMeasB : AEStronglyMeasurable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s))
      (volume.restrict
        (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hBoundB : ∀ᵐ r ∂volume,
      r ∈ Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi →
      ∀ t ∈ T,
        ‖originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSourceDot
            a ell c z b w Z Fdot Sdot Pdot t) r‖ ≤ boundB r)
    (hBoundIntB : IntervalIntegrable boundB volume
      (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hMovingIntB : ∀ t ∈ T,
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
    (hG : 0 ≤ G) (hBR : hi ≤ scale)
    (hSliver : ∀ t ∈ T, ∀ x ∈ uIoc
      (actualHartreeOnePhysicalMovingGreenLower ell a t)
      (actualHartreeOnePhysicalMovingGreenLower ell a s),
      0 < x ∧ x ≤ hi ∧ ‖K.x x‖ ≤ G ∧ ‖K.y x‖ ≤ G)
    (hSourceTime : ∀ t ∈ T,
      ∀ x ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
      ∀ τ ∈ Icc (min s t) (max s t),
        ∃ d : ℂ,
          HasDerivAt
            (fun u => actualHartreeTrueMovingAdjustedSource
              a ell c z b w Z u x) d τ ∧
          ‖d‖ ≤ D) :
    HasDerivAt
      (fun t => actualSingularGreenCoeff K
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) hi)
      (actualSingularGreenCoeff K
        (actualHartreeOnePhysicalMovingGreenLower ell a s)
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s) hi +
        (((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
           ellDot * a s -
          actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2) •
          (-originGreenSourceA K
            (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s)
            (actualHartreeOnePhysicalMovingGreenLower ell a s))) s
    ∧
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
  have hRatioA :
      ∀ t ∈ T, ∀ x ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
      ‖originPhysicalValue K.x x / originGreenWronskian K x‖ ≤
        G * hi := by
    intro t ht x hx
    rcases hSliver t ht x hx with ⟨hxpos, hxhi, hxX, hxY⟩
    exact (actual_Hartree_original_both_Green_density_ratios_no_left_radius
      K G hi x hG hxpos hxhi hBR hxX hxY).1
  have hRatioB :
      ∀ t ∈ T, ∀ x ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
      ‖originPhysicalValue K.y x / originGreenWronskian K x‖ ≤
        G * hi := by
    intro t ht x hx
    rcases hSliver t ht x hx with ⟨hxpos, hxhi, hxX, hxY⟩
    exact (actual_Hartree_original_both_Green_density_ratios_no_left_radius
      K G hi x hG hxpos hxhi hBR hxX hxY).2
  constructor
  · exact actual_Hartree_one_physical_selected_singular_Green_joint_derivative_from_original_sources
      K hBasis hlohi hHi ell a c z b w Z bdot wdot Zdot
      Fdot Sdot Pdot s ellDot aDot (G * hi) D T boundA
      hT hEll hA hEllPos ha hr0 hFcont haT hb hw hZ
      hColumns hDet hPhysicalDeriv hMeasA hSourceIntA
      hDotMeasA hBoundA hBoundIntA hMovingIntA
      hRatioA hSourceTime
  · exact actual_Hartree_one_physical_selected_Green_joint_derivative_from_original_sources
      K hBasis hlohi hHi ell a c z b w Z bdot wdot Zdot
      Fdot Sdot Pdot s ellDot aDot (G * hi) D T boundB
      hT hEll hA hEllPos ha hr0 hFcont haT hb hw hZ
      hColumns hDet hPhysicalDeriv hMeasB hSourceIntB
      hDotMeasB hBoundB hBoundIntB hMovingIntB
      hRatioB hSourceTime

end HBL.TypeIIDynamicSelection
