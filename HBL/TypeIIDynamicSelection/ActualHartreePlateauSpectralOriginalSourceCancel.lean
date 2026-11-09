import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedPlateauSource
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralOriginalPDEMismatch
import Mathlib.Tactic

/-!
# Actual original Hartree source cancels throughout the inner plateau

The original quartic interaction, its two physical speed directions,
and both genuine conjugated Fredholm channels agree on 0<y<=L.
After a zero-left-jet spectral Green correction the exact ORIGINAL
unshifted Kummer operator therefore has only the explicit first-order
spectral mismatch -a^{-2}*delta*u0 on this plateau.

The statement does not pretend that the shifted quadratic spectral
defect bounds the original PDE, nor assume any decay for delta,
the moving basis or the genuine modulation trajectory.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- On the true physical source plateau, the ONLY spectral
mismatch in the ORIGINAL unshifted source is first-order. -/
theorem actual_Hartree_plateau_spectral_original_source_exact_cancel
    (a ell c : ℝ) (z : ℝ → ℂ) (y db dw : ℝ)
    (ha : 0 < a) (hL : 0 < actualHartreeSlowInnerRadius ell)
    (hy : 0 < y) (hyL : y ≤ actualHartreeSlowInnerRadius ell)
    (u0 : ℝ → ℂ) (delta : ℂ) :
    let L := actualHartreeSlowInnerRadius ell
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    let Fo : ℝ → ℂ := fun r =>
      -actualHartreeLaplacianScaledKummerSource a ell c z r -
        (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
        (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
    ((a ^ 2)⁻¹ : ℝ) •
        (Fo (y / a) - delta * u0 (y / a)) +
      actualHartreeTwoChannelPhysicalSource
        (fun r => Fp r + dw * Gp r)
        (fun r => Fm r + db * Gm r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by
  dsimp only
  have hPlateau :=
    actual_Hartree_moment_locked_plateau_scaled_source
      a ell c z y db dw ha hL hy hyL
  dsimp only at hPlateau
  have hLinear :
      ((a ^ 2)⁻¹ : ℝ) •
          ((-actualHartreeLaplacianScaledKummerSource a ell c z (y / a) -
              (db : ℂ) * actualMomentLockedScaledScaleSource a c (y / a) -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c (y / a)) -
            delta * u0 (y / a)) +
        actualHartreeTwoChannelPhysicalSource
          (fun r => actualHartreeTransmissionPlusSource ell c z r +
            dw * actualMomentLockedInnerPhaseSource
              (actualHartreeSlowInnerRadius ell) c r)
          (fun r => actualHartreeTransmissionMinusSource ell c z r +
            db * actualMomentLockedInnerScaleSource
              (actualHartreeSlowInnerRadius ell) c r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by
    rw [smul_sub]
    calc
      _ = (((a ^ 2)⁻¹ : ℝ) •
            (-actualHartreeLaplacianScaledKummerSource a ell c z (y / a) -
              (db : ℂ) * actualMomentLockedScaledScaleSource a c (y / a) -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c (y / a)) +
           actualHartreeTwoChannelPhysicalSource
            (fun r => actualHartreeTransmissionPlusSource ell c z r +
              dw * actualMomentLockedInnerPhaseSource
                (actualHartreeSlowInnerRadius ell) c r)
            (fun r => actualHartreeTransmissionMinusSource ell c z r +
              db * actualMomentLockedInnerScaleSource
                (actualHartreeSlowInnerRadius ell) c r) y) -
          ((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by abel
      _ = _ := by rw [hPlateau]; simp
  exact hLinear

/-- Full ORIGINAL Kummer PDE, not the shifted spectral operator. This
exact identity retains the first-order spectral source; neither its
positive time order nor a norm bound is asserted here. -/
theorem actual_Hartree_plateau_original_Kummer_PDE_spectral_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a ell c B : ℝ) (z : ℝ → ℂ) (db dw : ℝ)
    (ha : 0 < a) (hell : 0 < ell) (hL : 0 < actualHartreeSlowInnerRadius ell)
    (hOrder : actualHartreeSlowInnerRadius ell / a ≤ B)
    (hB : B < scale)
    (U DU delta : ℂ)
    (hFoCont : ∀ r ∈ Ioo (0 : ℝ) scale,
      ContinuousAt
        (fun t => -actualHartreeLaplacianScaledKummerSource a ell c z t -
          (db : ℂ) * actualMomentLockedScaledScaleSource a c t -
          (dw : ℂ) * actualMomentLockedScaledPhaseSource a c t) r)
    (y : ℝ) (hy : 0 < y) (hyL : y ≤ actualHartreeSlowInnerRadius ell)
    (hyRange : y < a * scale) :
    let L := actualHartreeSlowInnerRadius ell
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    let Fo : ℝ → ℂ := fun r =>
      -actualHartreeLaplacianScaledKummerSource a ell c z r -
        (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
        (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
    let u0 := actualOriginMatchedKummerValue K (L / a) B Fo U DU
    actualMatchedScaledKummerApply mu theta a
      (actualHartreeMatchedSpectralPhysicalValue K a (L / a) B
        Fo U DU delta) y +
      actualHartreeTwoChannelPhysicalSource
        (fun r => Fp r + dw * Gp r)
        (fun r => Fm r + db * Gm r) y =
      -((a ^ 2)⁻¹ : ℝ) • (delta * u0 (y / a)) := by
  dsimp only
  have hr0 : 0 < actualHartreeSlowInnerRadius ell / a :=
    div_pos hL ha
  have hPDE :=
    actual_Hartree_matched_spectral_original_physical_source
      K a (actualHartreeSlowInnerRadius ell / a) B
      ha hr0 hOrder hB
      (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
        (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
        (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r)
      hFoCont U DU delta y ⟨hy, hyRange⟩
  have hCancel :=
    actual_Hartree_plateau_spectral_original_source_exact_cancel
      a ell c z y db dw ha hL hy hyL
      (actualOriginMatchedKummerValue K (actualHartreeSlowInnerRadius ell / a) B
        (fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r -
          (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
          (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r) U DU)
      delta
  dsimp only at hCancel hPDE
  rw [hPDE]
  exact hCancel

end HBL.TypeIIDynamicSelection
