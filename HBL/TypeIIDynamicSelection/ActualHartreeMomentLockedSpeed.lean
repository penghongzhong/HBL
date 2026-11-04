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

/-- The actual globally truncated monopole, including c=0. -/
def actualMomentLockedCore (c : ℝ) : ℝ → ℝ :=
  monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c

/-- Actual amplitude tangent; the moving-cutoff derivative is retained. -/
def actualMomentLockedAmplitudeTangent (c r : ℝ) : ℝ :=
  monopoleRadialProfile r *
    (1-cutoff (|c|*r/4)-(|c|*r/4)*deriv cutoff (|c|*r/4))

/-- This is the effective scale direction after imposing the TRUE moment law. -/
def actualMomentLockedScaleProfile (c r : ℝ) : ℝ :=
  dilationGenerator (actualMomentLockedCore c) r -
    c * actualMomentLockedAmplitudeTangent c r

def actualMomentLockedScaleSource (c r : ℝ) : ℂ :=
  Complex.I * (actualMomentLockedScaleProfile c r : ℂ)

def actualMomentLockedPhaseSource (c r : ℝ) : ℂ :=
  (actualMomentLockedCore c r : ℂ)

/-- The remaining source contains the FULL nonlocal core nonlinearity and
actual moment variation. It is not a freely assigned layer source. -/
def actualMomentLockedSpatialSource (c m r : ℝ) : ℂ :=
  complexRadialLaplacian (fun x => (actualMomentLockedCore c x : ℂ)) r +
    complexRadialHartreeNonlinearity (fun x => (actualMomentLockedCore c x : ℂ)) r +
    Complex.I * (m * actualMomentLockedAmplitudeTangent c r : ℝ)

/-- Exact cancellation of all cutoff-derivative terms in the physical scale
coefficient, with no strict-core restriction or assumption c != 0. -/
theorem actual_Hartree_moment_locked_scale_cutoff_cancellation
    (c r : ℝ) (hr : 0 < r) :
    actualMomentLockedScaleProfile c r =
      dilationGenerator bubble r + c * (1-cutoff (|c|*r/4)) *
        (dilationGenerator monopoleRadialProfile r-monopoleRadialProfile r) := by
  have h := monopoleMovingCutoff_dilation_eq c hr
  dsimp [actualMomentLockedScaleProfile, actualMomentLockedCore,
    actualMomentLockedAmplitudeTangent]
  linear_combination h

/-- Both true speed profiles are globally O(|c|)-close to the actual bubble
speed profiles. The constant is chosen before c and r and uses only already
constructed monopole bounds; it does not use a bound on cutoff derivatives. -/
theorem actual_Hartree_moment_locked_speed_profiles_uniform_close :
    ∃ M : ℝ, 0 < M ∧ ∀ c r : ℝ, 0 < r →
      |actualMomentLockedScaleProfile c r-dilationGenerator bubble r| ≤ M*|c| ∧
      |actualMomentLockedCore c r-bubble r| ≤ M*|c| := by
  obtain ⟨D,hD,hDil⟩ := monopoleRadialProfile_dilation_bounded
  have hP : 0 < monopoleRadialBoundConstant := monopoleRadialBoundConstant_pos
  let M : ℝ := D+monopoleRadialBoundConstant
  have hM : 0 < M := by dsimp [M]; linarith
  refine ⟨M,hM,?_⟩
  intro c r hr
  have hlo : 0 ≤ cutoff (|c|*r/4) := Real.smoothTransition.nonneg _
  have hhi : cutoff (|c|*r/4) ≤ 1 := Real.smoothTransition.le_one _
  have heta : |1-cutoff (|c|*r/4)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
    linarith
  have hEtaMul : |c*(1-cutoff (|c|*r/4))| ≤ |c| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left heta (abs_nonneg c)).trans_eq (mul_one _)
  have hDiff : |dilationGenerator monopoleRadialProfile r-monopoleRadialProfile r| ≤ M :=
    (abs_sub _ _).trans (_root_.add_le_add (hDil r hr) (monopoleRadialProfile_abs_le hr))
  constructor
  · rw [actual_Hartree_moment_locked_scale_cutoff_cancellation c r hr, add_sub_cancel_left,
      abs_mul]
    exact (mul_le_mul hEtaMul hDiff (abs_nonneg _) (abs_nonneg c)).trans_eq (mul_comm _ _)
  · have hCore : actualMomentLockedCore c r-bubble r =
        c*(1-cutoff (|c|*r/4))*monopoleRadialProfile r := by
      unfold actualMomentLockedCore
      rw [monopoleMovingCutoffProfile_eq]
      ring
    rw [hCore,abs_mul]
    have hpM : |monopoleRadialProfile r| ≤ M :=
      (monopoleRadialProfile_abs_le hr).trans (by dsimp [M]; linarith)
    exact (mul_le_mul hEtaMul hpM (abs_nonneg _) (abs_nonneg c)).trans_eq (mul_comm _ _)

/-- The actual core residual after a moment-locked amplitude derivative.
This is an exact equality for the ORIGINAL nonlocal differential expression.
The amplitude law is exposed here for reuse; the next theorem derives it
from the genuine three-dimensional radiation moment and clock. -/
theorem actual_Hartree_core_residual_moment_locked_speed_split
    (c : ℝ → ℝ) (b omega m s r : ℝ) (hr : 0 < r)
    (hc : HasDerivAt c (-b*c s+m) s) :
    complexRadialRenormalizedResidual
      (fun t x => (actualMomentLockedCore (c t) x : ℂ)) b omega s r =
      actualMomentLockedSpatialSource (c s) m r +
        (b : ℂ)*actualMomentLockedScaleSource (c s) r +
        (omega : ℂ)*actualMomentLockedPhaseSource (c s) r := by
  have hTime := (monopoleMovingCutoffTime_hasDerivAt hc r).ofReal_comp
  have hTime' : deriv (fun t => (actualMomentLockedCore (c t) r : ℂ)) s =
      (((-b*c s+m)*actualMomentLockedAmplitudeTangent (c s) r : ℝ) : ℂ) := by
    convert hTime.deriv using 1
    · rfl
    · congr 1
      unfold actualMomentLockedAmplitudeTangent
      ring
  have hSpace : DifferentiableAt ℝ (actualMomentLockedCore (c s)) r :=
    (monopoleMovingCutoffSpatial_hasDerivAt (c s) hr).differentiableAt
  unfold complexRadialRenormalizedResidual
  rw [hTime',complexRadialDilation_ofReal hSpace]
  unfold actualMomentLockedSpatialSource actualMomentLockedScaleSource
    actualMomentLockedScaleProfile actualMomentLockedPhaseSource
  push_cast
  ring

/-- No free monopole speed is introduced: the coefficient m is supplied
by the genuine 3D radiation moment and the true scale/clock identities. -/
theorem actual_Hartree_threeD_moment_core_speed_split
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (omega : ℝ) {s dm r : ℝ} (hr : 0 < r)
    (hEll : HasDerivAt ell (-(b s*ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s)^2) s)
    (hMoment : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s)) :
    complexRadialRenormalizedResidual
      (fun t x => (actualMomentMonopoleProfile ell z time t x : ℂ))
      (b s) omega s r =
      actualMomentLockedSpatialSource
        (actualPhysicalRadiationMonopole ell z time s)
        (hartreeKappa*(ell s)^3*dm) r +
      (b s : ℂ)*actualMomentLockedScaleSource
        (actualPhysicalRadiationMonopole ell z time s) r +
      (omega : ℂ)*actualMomentLockedPhaseSource
        (actualPhysicalRadiationMonopole ell z time s) r := by
  exact actual_Hartree_core_residual_moment_locked_speed_split
    (actualPhysicalRadiationMonopole ell z time) (b s) omega
    (hartreeKappa*(ell s)^3*dm) s r hr
    (actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
      ell b z time hEll hEllPos hTime hMoment)

/-- The original spatial cutoff and amplitude give the true bubble reference,
not two arbitrary auxiliary functions with normalized projections. -/
theorem actual_Hartree_moment_locked_zero_reference (r : ℝ) (hr : 0 < r) :
    actualMomentLockedScaleSource 0 r =
      Complex.I*(dilationGenerator bubble r : ℂ) ∧
    actualMomentLockedPhaseSource 0 r = (bubble r : ℂ) := by
  constructor
  · unfold actualMomentLockedScaleSource
    rw [actual_Hartree_moment_locked_scale_cutoff_cancellation 0 r hr]
    simp
  · unfold actualMomentLockedPhaseSource actualMomentLockedCore
    rw [monopoleMovingCutoffProfile_eq]
    simp

end HBL.TypeIIDynamicSelection
