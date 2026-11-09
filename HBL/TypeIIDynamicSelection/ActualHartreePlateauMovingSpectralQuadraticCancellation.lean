import HBL.TypeIIDynamicSelection.ActualHartreeMovingCoefficientSpectralPhysicalPDE
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedPlateauSource
import Mathlib.Tactic

/-!
# The original Hartree plateau source and current spectral coefficient agree

On the genuine same-source physical plateau, the original quartic Hartree
Riesz forcing, the two physical Fredholm channels, and their modulation
speed sources cancel. The fixed reference Kummer operator on the
spectrally corrected field has a first-order source -delta*u0.
The ACTUAL moving-coefficient operator contributes +delta*w_delta,
so the exact remaining source is -delta*u1, with
u1=G_K0[delta*u0] having the zero initial Cauchy jet.

The first-order cancellation is an exact consequence of the physical
coefficient difference, not a smallness assumption or a substitution of
a shifted-operator defect into the original PDE. This is still a
fixed-slice Kummer-region statement; no time gain, endpoint derivatives,
full four-zone nonlinear Hartree remainder or Type-II rate is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual Hartree source cancellation and current-moving spectral
coefficient leave EXACTLY the quadratic Volterra source -delta*u1
on the physical inner plateau, with no inserted residual-order bound. -/
theorem actual_Hartree_plateau_current_moving_spectrum_exact_quadratic_source
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a ell c B db dw y : ℝ) (z : ℝ → ℂ)
    (ha : 0 < a)
    (hL : 0 < actualHartreeSlowInnerRadius ell)
    (hOrder : actualHartreeSlowInnerRadius ell / a ≤ B)
    (hB : B < scale)
    (hFoCont : ∀ r ∈ Ioo (0 : ℝ) scale,
      ContinuousAt
        (fun t => -actualHartreeLaplacianScaledKummerSource a ell c z t -
          (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
          (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r)
    (hy : 0 < y) (hyL : y ≤ actualHartreeSlowInnerRadius ell)
    (hyRange : y < a * scale)
    (U DU : ℂ) :
    let L := actualHartreeSlowInnerRadius ell
    let Fo : ℝ → ℂ := fun r =>
      -actualHartreeLaplacianScaledKummerSource a ell c z r -
        (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
        (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
    let delta : ℂ :=
      frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0
    let q := actualHartreeMatchedSpectralFirstSource
      K (L / a) B Fo U DU delta
    let u1 := actualOriginMatchedKummerValue K (L / a) B q 0 0
    actualMatchedScaledKummerApply mu theta a
      (actualHartreeMatchedSpectralPhysicalValue
        K a (L / a) B Fo U DU delta) y +
      actualHartreeTwoChannelPhysicalSource
        (fun r => actualHartreeTransmissionPlusSource ell c z r +
          dw * actualMomentLockedInnerPhaseSource L c r)
        (fun r => actualHartreeTransmissionMinusSource ell c z r +
          db * actualMomentLockedInnerScaleSource L c r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u1 (y / a)) := by
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fo : ℝ → ℂ := fun r =>
    -actualHartreeLaplacianScaledKummerSource a ell c z r -
      (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
  let delta : ℂ := frozenZeroCoeff mu theta -
    frozenZeroCoeff mu0 theta0
  let q := actualHartreeMatchedSpectralFirstSource K (L / a) B Fo U DU delta
  let u1 := actualOriginMatchedKummerValue K (L / a) B q 0 0
  have hr0 : 0 < L / a := div_pos hL ha
  have hMoving :=
    actual_Hartree_moving_coefficient_spectral_physical_PDE_exact
      K mu theta a (L / a) B ha hr0 hOrder hB
      Fo hFoCont U DU y ⟨hy, hyRange⟩
  have hPlateau :=
    actual_Hartree_moment_locked_plateau_scaled_source
      a ell c z y db dw ha hL hy hyL
  dsimp only at hMoving hPlateau
  change actualMatchedScaledKummerApply mu theta a
      (actualHartreeMatchedSpectralPhysicalValue
        K a (L / a) B Fo U DU delta) y +
      actualHartreeTwoChannelPhysicalSource
        (fun r => actualHartreeTransmissionPlusSource ell c z r +
          dw * actualMomentLockedInnerPhaseSource L c r)
        (fun r => actualHartreeTransmissionMinusSource ell c z r +
          db * actualMomentLockedInnerScaleSource L c r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u1 (y / a))
  rw [hMoving]
  calc
    ((a ^ 2)⁻¹ : ℝ) • (Fo (y / a) - delta * u1 (y / a)) +
      actualHartreeTwoChannelPhysicalSource
        (fun r => actualHartreeTransmissionPlusSource ell c z r +
          dw * actualMomentLockedInnerPhaseSource L c r)
        (fun r => actualHartreeTransmissionMinusSource ell c z r +
          db * actualMomentLockedInnerScaleSource L c r) y =
      (((a ^ 2)⁻¹ : ℝ) • Fo (y / a) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => actualHartreeTransmissionPlusSource ell c z r +
            dw * actualMomentLockedInnerPhaseSource L c r)
          (fun r => actualHartreeTransmissionMinusSource ell c z r +
            db * actualMomentLockedInnerScaleSource L c r) y) -
        ((a ^ 2)⁻¹ : ℝ) • (delta * u1 (y / a)) := by
      rw [smul_sub]
      abel
    _ = -((a ^ 2)⁻¹ : ℝ) • (delta * u1 (y / a)) := by
      rw [hPlateau]
      simp

end HBL.TypeIIDynamicSelection
