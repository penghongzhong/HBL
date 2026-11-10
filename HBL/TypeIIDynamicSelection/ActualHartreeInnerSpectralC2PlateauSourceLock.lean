import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedPlateauSource
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralOriginalPDEMismatch
import Mathlib.Tactic

/-!
# Actual same-PDE plateau source cancels in the INNER spectral C² mismatch

The original source is the *literal* inverse-square quartic Hartree
interaction with its actual two real modulation-speed directions.
Both inner Fredholm channels and the origin-normalized Kummer
source use this same full original physical interaction.

The existing strict plateau identification cancels the two
unshifted source terms pointwise even at the inner Cauchy join.
After spectral correction, the ONLY extra source in this
identification is the *actual* delta times the original
Cramer Green field. No curvature, derivative bound, time order,
physical orbit or Type-II rate is postulated here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- At every actual inner plateau point, the literal original Hartree
two-channel source cancels the true physical outer source. The source
left after the first spectral correction is exactly the correction
coefficient times the SAME original source-normalized Cramer Green
solution; no independent source is introduced. -/
theorem actual_Hartree_original_plateau_spectral_inner_C2_source_cancellation
    (a ell c : ℝ) (z : ℝ → ℂ) (y db dw : ℝ)
    (ha : 0 < a)
    (hL : 0 < actualHartreeSlowInnerRadius ell)
    (hy : 0 < y) (hyL : y ≤ actualHartreeSlowInnerRadius ell)
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (B : ℝ) (U DU delta : ℂ) :
    let L := actualHartreeSlowInnerRadius ell
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    let Fo : ℝ → ℂ := fun r =>
      -actualHartreeLaplacianScaledKummerSource a ell c z r -
      (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
    let u0 := actualOriginMatchedKummerValue K (y / a) B Fo U DU
    ((a ^ 2)⁻¹ : ℝ) • (Fo (y / a) - delta * u0 (y / a)) +
      actualHartreeTwoChannelPhysicalSource
        (fun r => Fp r + dw * Gp r)
        (fun r => Fm r + db * Gm r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fp := actualHartreeTransmissionPlusSource ell c z
  let Fm := actualHartreeTransmissionMinusSource ell c z
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let Fo : ℝ → ℂ := fun r =>
    -actualHartreeLaplacianScaledKummerSource a ell c z r -
    (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
    (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
  let u0 := actualOriginMatchedKummerValue K (y / a) B Fo U DU
  have hSame :
      ((a ^ 2)⁻¹ : ℝ) • Fo (y / a) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y = 0 := by
    exact actual_Hartree_moment_locked_plateau_scaled_source
      a ell c z y db dw ha hL hy hyL
  change ((a ^ 2)⁻¹ : ℝ) •
      (Fo (y / a) - delta * u0 (y / a)) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a))
  rw [smul_sub]
  calc
    ((a ^ 2)⁻¹ : ℝ) • Fo (y / a) -
        ((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y =
      (((a ^ 2)⁻¹ : ℝ) • Fo (y / a) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => Fp r + dw * Gp r)
          (fun r => Fm r + db * Gm r) y) -
        ((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by abel
    _ = -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by rw [hSame]; simp


/-- At a genuine C¹ inner interface the ORIGINAL physical Kummer
operator's source jump is exactly the radial curvature jump.
All drift, potential and parameter-dependent coefficients cancel.
This does not claim that the original Fredholm Hessian is this Kummer
operator; identifying that physical source remains a separate gate. -/
theorem actual_Hartree_inner_C1_curvature_jump_eq_original_source_jump
    (mu theta a L : ℝ) (u v : ℝ → ℂ)
    (hValue : u L = v L)
    (hSlope : deriv u L = deriv v L) :
    deriv (deriv u) L - deriv (deriv v) L =
      actualMatchedScaledKummerApply mu theta a u L -
        actualMatchedScaledKummerApply mu theta a v L := by
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  simp only [Complex.real_smul, hValue, hSlope]
  ring

/-- If the INNER original source and the spectrally corrected OUTER
original source have the exact first-order delta*u0 discrepancy,
their C¹ splice has precisely that second-jet defect. In particular
the first-order ORIGINAL PDE residual cannot be silently replaced by
a quadratic shifted-operator residual. No independent source bound
or a physical-orbit realization is assumed. -/
theorem actual_Hartree_inner_C1_spectral_curvature_jump_from_sources
    (mu theta a L : ℝ) (u v : ℝ → ℂ)
    (S delta u0 : ℂ)
    (hValue : u L = v L)
    (hSlope : deriv u L = deriv v L)
    (hInnerSource : actualMatchedScaledKummerApply mu theta a u L = S)
    (hCorrectedSource :
      actualMatchedScaledKummerApply mu theta a v L =
        S - ((a ^ 2)⁻¹ : ℝ) • (delta * u0)) :
    deriv (deriv u) L - deriv (deriv v) L =
      ((a ^ 2)⁻¹ : ℝ) • (delta * u0) := by
  rw [actual_Hartree_inner_C1_curvature_jump_eq_original_source_jump
    mu theta a L u v hValue hSlope, hInnerSource, hCorrectedSource]
  simp only [Complex.real_smul]
  ring

end HBL.TypeIIDynamicSelection
