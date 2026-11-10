import HBL.TypeIIDynamicSelection.ActualOriginGreenMovingSingularChannel
import HBL.TypeIIDynamicSelection.ActualHartreeOnePhysicalMovingGreenJoint
import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingSelectedRegularGreenDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Both genuine moving-Hartree source and moving lower endpoint for singular A

This is the missing companion of the original regular B Green coefficient.
It uses the SAME nonlocal quartic Hartree interaction and exact real
Cramer-selected modulation pair, and the real slow-inner endpoint
r0(s)=ell(s)^(-1/16)/a(s). The temporal derivative of the selected
source is DERIVED from the actual three physical source derivatives.

The original integrable temporal majorant, spatial Wronskian ratio,
and actual time-slice differentiability remain explicit hypotheses.
No positive time gain, shell decay, or blowup rate is inserted.
-/ 

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology Interval
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_moving_selected_singular_Green_hasDerivAt
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 B s : ℝ)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z bdot wdot Zdot : ℝ → ℂ)
    (Fdot Sdot Pdot : ℝ → ℝ → ℂ)
    (T : Set ℝ) (bound : ℝ → ℝ)
    (hT : T ∈ 𝓝 s)
    (hB : 0 < B)
    (ha : ∀ t ∈ T, 0 < a t)
    (hb : ∀ t ∈ T, HasDerivAt b (bdot t) t)
    (hw : ∀ t ∈ T, HasDerivAt w (wdot t) t)
    (hZ : ∀ t ∈ T, HasDerivAt Z (Zdot t) t)
    (hColumns : ∀ t ∈ T,
      ‖b t‖ ≤ a t * B ^ 2 ∧ ‖w t‖ ≤ a t * B ^ 2)
    (hDet : ∀ t ∈ T,
      (a t) ^ 2 * B ^ 4 / 256 ≤ actualRealCramerDet (b t) (w t))
    (hPhysicalDeriv : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
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
        (originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
        (volume.restrict (Ι r0 B)))
    (hInt : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume r0 B)
    (hDotMeas : AEStronglyMeasurable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s))
      (volume.restrict (Ι r0 B)))
    (hBound : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ T,
        ‖originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSourceDot
            a ell c z b w Z Fdot Sdot Pdot t) r‖ ≤ bound r)
    (hBoundInt : IntervalIntegrable bound volume r0 B) :
    HasDerivAt
      (fun t => actualSingularGreenCoeff K r0
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) B)
      (actualSingularGreenCoeff K r0
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s) B) s := by
  apply actual_origin_SingularGreen_coeff_fixed_lower_source_hasDerivAt
    K r0 B s
    (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t)
    (fun t => actualHartreeTrueMovingAdjustedSourceDot
      a ell c z b w Z Fdot Sdot Pdot t)
    T bound hT hMeas hInt hDotMeas hBound hBoundInt
  filter_upwards [hPhysicalDeriv] with r hr
  intro hrmem t ht
  obtain ⟨hF, hS, hP⟩ := hr hrmem t ht
  have hCramer :=
    actual_Hartree_true_moving_adjusted_source_derivative
      a ell c z b w Z t r (a t) B (ha t ht) hB
      (bdot t) (wdot t) (Zdot t)
      (Fdot t r) (Sdot t r) (Pdot t r)
      (hb t ht) (hw t ht) (hZ t ht)
      (hColumns t ht).1 (hColumns t ht).2 (hDet t ht)
      hF hS hP
  obtain ⟨pbDot, pwDot, hpb, hpw, _hSpeed, hPhysical⟩ := hCramer
  have hpbEq :
      deriv (fun u =>
        (actualRealCramerCorrection (b u) (w u) (Z u)).1) t = pbDot :=
    hpb.deriv
  have hpwEq :
      deriv (fun u =>
        (actualRealCramerCorrection (b u) (w u) (Z u)).2) t = pwDot :=
    hpw.deriv
  simpa only [actualHartreeTrueMovingAdjustedSourceDot, hpbEq, hpwEq] using
    hPhysical


theorem actual_Hartree_true_selected_singular_Green_density_time_MVT
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s t r C D : ℝ)
    (hRatio : ‖originPhysicalValue K.x r /
      originGreenWronskian K r‖ ≤ C)
    (hFullDerivative : ∀ τ ∈ Icc (min s t) (max s t),
      ∃ d : ℂ,
        HasDerivAt
          (fun u => actualHartreeTrueMovingAdjustedSource
            a ell c z b w Z u r) d τ ∧
        ‖d‖ ≤ D) :
    ‖originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) r -
      originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) r‖ ≤
      (C * D) * |t-s| := by
  let F : ℝ → ℂ := fun τ =>
    actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ r
  let q : ℂ := originPhysicalValue K.x r / originGreenWronskian K r
  let H : ℝ → ℂ := fun τ => F τ * q
  have hHValue (τ : ℝ) :
      originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ) r =
        H τ := by
    dsimp [H, F, q, originGreenSourceA]
    ring
  have hDiff : ∀ τ ∈ Icc (min s t) (max s t),
      ∃ d : ℂ, HasDerivAt H d τ ∧ ‖d‖ ≤ C * D := by
    intro τ hτ
    obtain ⟨d, hd, hD⟩ := hFullDerivative τ hτ
    have hdH : HasDerivAt H (d * q) τ := by
      exact hd.mul_const q
    have hDpos : 0 ≤ D := (norm_nonneg d).trans hD
    have hNorm : ‖d * q‖ ≤ C * D := by
      calc
        ‖d * q‖ = ‖d‖ * ‖q‖ := norm_mul _ _
        _ ≤ D * C := by
          have hq : ‖q‖ ≤ C := hRatio
          exact mul_le_mul hD hq (norm_nonneg _) hDpos
        _ = C * D := by ring
    exact ⟨d * q, hdH, hNorm⟩
  have hHdiff : ∀ τ ∈ Icc (min s t) (max s t),
      DifferentiableAt ℝ H τ := by
    intro τ hτ
    obtain ⟨d, hd, _⟩ := hDiff τ hτ
    exact hd.differentiableAt
  have hHbound : ∀ τ ∈ Icc (min s t) (max s t),
      ‖deriv H τ‖ ≤ C * D := by
    intro τ hτ
    obtain ⟨d, hd, hdBound⟩ := hDiff τ hτ
    simpa only [hd.deriv] using hdBound
  have hs : s ∈ Icc (min s t) (max s t) :=
    ⟨min_le_left _ _, le_max_left _ _⟩
  have ht : t ∈ Icc (min s t) (max s t) :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  have hMVT :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      hHdiff hHbound (convex_Icc _ _) hs ht
  rw [hHValue t, hHValue s]
  simpa only [Real.norm_eq_abs] using hMVT


theorem actual_Hartree_one_physical_selected_singular_Green_joint_derivative_from_original_sources
    {mu theta scale lo hi basisBound : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hBasis : OriginBasisOn K lo hi basisBound)
    (hlohi : lo < hi) (hHi : 0 < hi)
    (ell a c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z bdot wdot Zdot : ℝ → ℂ)
    (Fdot Sdot Pdot : ℝ → ℝ → ℂ)
    (s ellDot aDot CK D : ℝ)
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
        (originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
        (volume.restrict
          (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hSourceInt : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hDotMeas : AEStronglyMeasurable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSourceDot
          a ell c z b w Z Fdot Sdot Pdot s))
      (volume.restrict
        (Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)))
    (hBound : ∀ᵐ r ∂volume,
      r ∈ Ι (actualHartreeOnePhysicalMovingGreenLower ell a s) hi →
      ∀ t ∈ T,
        ‖originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSourceDot
            a ell c z b w Z Fdot Sdot Pdot t) r‖ ≤ bound r)
    (hBoundInt : IntervalIntegrable bound volume
      (actualHartreeOnePhysicalMovingGreenLower ell a s) hi)
    (hMovingInt : ∀ t ∈ T,
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
    (hRatio : ∀ t ∈ T,
      ∀ x ∈ uIoc
        (actualHartreeOnePhysicalMovingGreenLower ell a t)
        (actualHartreeOnePhysicalMovingGreenLower ell a s),
      ‖originPhysicalValue K.x x / originGreenWronskian K x‖ ≤ CK)
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
            (actualHartreeOnePhysicalMovingGreenLower ell a s))) s := by
  have hSource :=
    actual_Hartree_true_moving_selected_singular_Green_hasDerivAt
      K (actualHartreeOnePhysicalMovingGreenLower ell a s) hi s
      a ell c z b w Z bdot wdot Zdot Fdot Sdot Pdot
      T bound hT hHi haT hb hw hZ hColumns hDet
      hPhysicalDeriv hMeas hSourceInt hDotMeas hBound hBoundInt
  let r0 : ℝ → ℝ := actualHartreeOnePhysicalMovingGreenLower ell a
  let rDot : ℝ :=
    ((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
        ellDot * a s -
      actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2
  have hR : HasDerivAt r0 rDot s :=
    actual_Hartree_slow_inner_Kummer_endpoint_time_derivative
      ell a s ellDot aDot hEll hA hEllPos ha
  have hEndpoint : HasDerivAt
      (fun t => actualSingularGreenCoeff K (r0 t)
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s) hi)
      (rDot • (-originGreenSourceA K
        (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s)
        (r0 s))) s := by
    exact actual_origin_Green_coeffA_moving_lower_hasDerivAt
      K hBasis hlohi
      (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s)
      hFcont r0 s rDot hr0 hR
  have hPhysicalDensityLip :
      ∀ t ∈ T, ∀ r ∈ uIoc (r0 t) (r0 s),
      ‖originGreenSourceA K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z t) r -
        originGreenSourceA K
          (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z s) r‖ ≤
        (CK * D) * |t-s| := by
    intro t ht r hr
    exact actual_Hartree_true_selected_singular_Green_density_time_MVT
      K a ell c z b w Z s t r CK D
      (hRatio t ht r hr) (hSourceTime t ht r hr)
  exact actual_origin_SingularGreen_moving_selected_joint_hasDerivAt
    K (actualHartreeOnePhysicalMovingGreenSource a ell c z b w Z) r0
    s hi (CK * D) rDot T hT hR
    hMovingInt hPhysicalDensityLip _ _ hSource hEndpoint

end HBL.TypeIIDynamicSelection
