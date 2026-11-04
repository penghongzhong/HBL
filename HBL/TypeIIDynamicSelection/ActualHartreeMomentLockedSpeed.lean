import HBL.TypeIIDynamicSelection.ActualMomentProfileDynamics
import HBL.MonopoleComplexResidual
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import Mathlib.Tactic

/-!
The radiation-moment amplitude is NOT a second free modulation parameter.
Its true law is c_s=-b*c+m, with m=kappa*ell^3*d_t(moment).
Thus the actual remaining core scale direction is i*(Lambda V_c-c*d_c V_c),
not i*d_c V_c and not i*Lambda V_c alone. The cutoff derivative cancels
EXACTLY in this direction, globally on r>0, including its moving transition.
The other coefficient is the original real phase coefficient omega.
The complete spatial Hartree operator and the moment-derivative forcing
are retained. No determinant, speed, boundary compatibility or time law
is assumed to have been solved by this source-identification result.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualMomentLockedCore (c : ℝ) : ℝ → ℝ :=
  monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c

def actualMomentLockedAmplitudeTangent (c r : ℝ) : ℝ :=
  monopoleRadialProfile r *
    (1 - cutoff (|c| * r / 4) - (|c| * r / 4) * deriv cutoff (|c| * r / 4))

/-- Effective scale profile after the TRUE moment law, not a free amplitude. -/
def actualMomentLockedScaleProfile (c r : ℝ) : ℝ :=
  dilationGenerator (actualMomentLockedCore c) r -
    c * actualMomentLockedAmplitudeTangent c r

def actualMomentLockedScaleSource (c r : ℝ) : ℂ :=
  Complex.I * (actualMomentLockedScaleProfile c r : ℂ)

def actualMomentLockedPhaseSource (c r : ℝ) : ℂ :=
  (actualMomentLockedCore c r : ℂ)

/-- Full nonlocal core operator and genuine moment variation are retained. -/
def actualMomentLockedSpatialSource (c m r : ℝ) : ℂ :=
  complexRadialLaplacian (fun x => (actualMomentLockedCore c x : ℂ)) r +
    complexRadialHartreeNonlinearity (fun x => (actualMomentLockedCore c x : ℂ)) r +
    Complex.I * (m * actualMomentLockedAmplitudeTangent c r : ℝ)

/-- The moving cutoff derivative cancels globally, including c=0. -/
theorem actual_Hartree_moment_locked_scale_cutoff_cancellation
    (c r : ℝ) (hr : 0 < r) :
    actualMomentLockedScaleProfile c r =
      dilationGenerator bubble r + c * (1 - cutoff (|c| * r / 4)) *
        (dilationGenerator monopoleRadialProfile r - monopoleRadialProfile r) := by
  have h := monopoleMovingCutoff_dilation_eq c hr
  dsimp [actualMomentLockedScaleProfile, actualMomentLockedCore,
    actualMomentLockedAmplitudeTangent]
  linear_combination h

/-- Both genuine profiles are globally O(|c|)-close to the bubble profiles.
The fixed constant is derived before c,r; no cutoff derivative bound is used. -/
theorem actual_Hartree_moment_locked_speed_profiles_uniform_close :
    ∃ M : ℝ, 0 < M ∧ ∀ c r : ℝ, 0 < r →
      |actualMomentLockedScaleProfile c r - dilationGenerator bubble r| ≤ M * |c| ∧
      |actualMomentLockedCore c r - bubble r| ≤ M * |c| := by
  obtain ⟨D,hD,hDil⟩ := monopoleRadialProfile_dilation_bounded
  have hP : 0 < monopoleRadialBoundConstant := monopoleRadialBoundConstant_pos
  let M : ℝ := D + monopoleRadialBoundConstant
  have hM : 0 < M := by dsimp [M]; linarith
  refine ⟨M,hM,?_⟩
  intro c r hr
  have hlo : 0 ≤ cutoff (|c| * r / 4) := Real.smoothTransition.nonneg _
  have hhi : cutoff (|c| * r / 4) ≤ 1 := Real.smoothTransition.le_one _
  have heta : |1 - cutoff (|c| * r / 4)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
    linarith
  have hEtaMul : |c * (1 - cutoff (|c| * r / 4))| ≤ |c| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left heta (abs_nonneg c)).trans_eq (mul_one _)
  have hDiff : |dilationGenerator monopoleRadialProfile r - monopoleRadialProfile r| ≤ M := by
    calc
      _ ≤ |dilationGenerator monopoleRadialProfile r| + |monopoleRadialProfile r| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (dilationGenerator monopoleRadialProfile r) (-monopoleRadialProfile r)
      _ ≤ M := _root_.add_le_add (hDil r hr) (monopoleRadialProfile_abs_le hr)
  constructor
  · rw [actual_Hartree_moment_locked_scale_cutoff_cancellation c r hr, add_sub_cancel_left,
      abs_mul]
    exact (mul_le_mul hEtaMul hDiff (abs_nonneg _) (abs_nonneg c)).trans_eq (mul_comm _ _)
  · have hCore : actualMomentLockedCore c r - bubble r =
        c * (1 - cutoff (|c| * r / 4)) * monopoleRadialProfile r := by
      unfold actualMomentLockedCore
      rw [monopoleMovingCutoffProfile_eq]
      ring
    rw [hCore, abs_mul]
    have hpM : |monopoleRadialProfile r| ≤ M :=
      (monopoleRadialProfile_abs_le hr).trans (by dsimp [M]; linarith)
    exact (mul_le_mul hEtaMul hpM (abs_nonneg _) (abs_nonneg c)).trans_eq (mul_comm _ _)

/-- Exact original core residual with the moment-locked amplitude derivative.
The next theorem supplies this amplitude law from the actual 3D moment. -/
theorem actual_Hartree_core_residual_moment_locked_speed_split
    (c : ℝ → ℝ) (b omega m s r : ℝ) (hr : 0 < r)
    (hc : HasDerivAt c (-(b * c s) + m) s) :
    complexRadialRenormalizedResidual
      (fun t x => (actualMomentLockedCore (c t) x : ℂ)) b omega s r =
      actualMomentLockedSpatialSource (c s) m r +
        (b : ℂ) * actualMomentLockedScaleSource (c s) r +
        (omega : ℂ) * actualMomentLockedPhaseSource (c s) r := by
  have hTime := (monopoleMovingCutoffTime_hasDerivAt hc r).ofReal_comp
  have hTime' : deriv (fun t => (actualMomentLockedCore (c t) r : ℂ)) s =
      (((-(b * c s) + m) * actualMomentLockedAmplitudeTangent (c s) r : ℝ) : ℂ) := by
    convert hTime.deriv using 1
    · rfl
    · congr 1
      unfold actualMomentLockedAmplitudeTangent
      ring
  have hSpace : DifferentiableAt ℝ (actualMomentLockedCore (c s)) r :=
    (monopoleMovingCutoffSpatial_hasDerivAt (c s) hr).differentiableAt
  unfold complexRadialRenormalizedResidual
  rw [hTime', complexRadialDilation_ofReal hSpace]
  unfold actualMomentLockedSpatialSource actualMomentLockedScaleSource
    actualMomentLockedScaleProfile actualMomentLockedPhaseSource
  push_cast
  ring

/-- The genuine 3D radiation moment fixes the amplitude derivative; there
is no independently adjustable c_s and no imposed Type-II exponent. -/
theorem actual_Hartree_threeD_moment_core_speed_split
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (omega : ℝ) {s dm r : ℝ} (hr : 0 < r)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s)^2) s)
    (hMoment : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s)) :
    complexRadialRenormalizedResidual
      (fun t x => (actualMomentMonopoleProfile ell z time t x : ℂ))
      (b s) omega s r =
      actualMomentLockedSpatialSource
        (actualPhysicalRadiationMonopole ell z time s)
        (hartreeKappa * (ell s)^3 * dm) r +
      (b s : ℂ) * actualMomentLockedScaleSource
        (actualPhysicalRadiationMonopole ell z time s) r +
      (omega : ℂ) * actualMomentLockedPhaseSource
        (actualPhysicalRadiationMonopole ell z time s) r := by
  exact actual_Hartree_core_residual_moment_locked_speed_split
    (actualPhysicalRadiationMonopole ell z time) (b s) omega
    (hartreeKappa * (ell s)^3 * dm) s r hr
    (actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
      ell b z time hEll hEllPos hTime hMoment)

/-- The reference directions really are the bubble's scale/phase directions. -/
theorem actual_Hartree_moment_locked_zero_reference (r : ℝ) (hr : 0 < r) :
    actualMomentLockedScaleSource 0 r =
      Complex.I * (dilationGenerator bubble r : ℂ) ∧
    actualMomentLockedPhaseSource 0 r = (bubble r : ℂ) := by
  constructor
  · unfold actualMomentLockedScaleSource
    rw [actual_Hartree_moment_locked_scale_cutoff_cancellation 0 r hr]
    simp
  · unfold actualMomentLockedPhaseSource actualMomentLockedCore
    rw [monopoleMovingCutoffProfile_eq]
    simp

end HBL.TypeIIDynamicSelection
