import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceTimeFromPhysicalScaledOrbit
import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import Mathlib.Tactic

/-!
# Physical full three-Riesz source => actual selected real speeds and time derivative

This theorem removes the previously independent derivative assumption
for the original nonlocal Hartree source in the REAL Cramer selected-speed
derivative. The original source-time derivative is produced by the
critical-scale Hartree interaction's three genuine radial logarithmic
Riesz potentials (mixed, pure-radiation, pure-core) under the original
physical fields' primitive C1 plus true integral-dominating hypotheses.

The same true source is then corrected by the real unique two-column
Cramer pair, including its two genuine modulation source directions.

The input time derivatives of these scale/phase physical DIRECTIONS,
and the original 3D density/integrability hypotheses, remain visible.
They are NOT replaced by a putative derivative of the already corrected
source, nor by any assumed Type-II blow-up exponent. This is a strict
one-orbit source-time theorem, not the full four-piece PDE residual.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The true full Hartree three-Riesz integral producer supplies the
original source derivative before the real Cramer speed is differentiated.
Neither original source-time derivative nor selected speed derivatives
are hypotheses. -/
theorem actual_Hartree_one_orbit_original_Riesz_produces_selected_source_derivative
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (dV : ℝ → ℝ → ℝ) (dZ : ℝ → ℝ → ℂ)
    (r s adot : ℝ) (hr : 0 < r)
    (hA : HasDerivAt a adot s) (ha : 0 < a s)
    (I : Set ℝ) (hI : I ∈ 𝓝 s) (hs : s ∈ I)
    (hV : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => actualHartreeTrueTwoStageScaledCore
        a c x rho) (dV t rho) t)
    (hZRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (actualHartreeTrueTwoStageScaledRadiation
        a ell z x rho).re) (dZ t rho).re t)
    (hZIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (actualHartreeTrueTwoStageScaledRadiation
        a ell z x rho).im) (dZ t rho).im t)
    (hZat : HasDerivAt
      (fun t => actualHartreeTrueTwoStageScaledRadiation a ell z t r)
      (dZ s r) s)
    (hMixMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeMixedRieszTimeIntegrand
          (actualHartreeTrueTwoStageScaledCore a c)
          (actualHartreeTrueTwoStageScaledRadiation a ell z) r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hMixInt : IntegrableOn
      (actualHartreeMixedRieszTimeIntegrand
        (actualHartreeTrueTwoStageScaledCore a c)
        (actualHartreeTrueTwoStageScaledRadiation a ell z) r s)
      (Ioi (0 : ℝ)))
    (hMixDotMeas : AEStronglyMeasurable
      (actualHartreeMixedRieszTimeVelocity
        (actualHartreeTrueTwoStageScaledCore a c) dV
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BM : ℝ → ℝ)
    (hBM : IntegrableOn BM (Ioi (0 : ℝ)))
    (hMixBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeMixedRieszTimeVelocity
        (actualHartreeTrueTwoStageScaledCore a c) dV
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r t rho|
        ≤ BM rho)
    (hZMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand
          (actualHartreeTrueTwoStageScaledRadiation a ell z) r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZInt : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand
        (actualHartreeTrueTwoStageScaledRadiation a ell z) r s)
      (Ioi (0 : ℝ)))
    (hZDotMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BZ : ℝ → ℝ) (hBZ : IntegrableOn BZ (Ioi (0 : ℝ)))
    (hZBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity
        (actualHartreeTrueTwoStageScaledRadiation a ell z) dZ r t rho|
          ≤ BZ rho)
    (hVMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand
          (fun τ rho =>
            (actualHartreeTrueTwoStageScaledCore a c τ rho : ℂ)) r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hVInt : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand
        (fun τ rho =>
          (actualHartreeTrueTwoStageScaledCore a c τ rho : ℂ)) r s)
      (Ioi (0 : ℝ)))
    (hVDotMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity
        (fun τ rho =>
          (actualHartreeTrueTwoStageScaledCore a c τ rho : ℂ))
        (fun τ rho => (dV τ rho : ℂ)) r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (BV : ℝ → ℝ) (hBV : IntegrableOn BV (Ioi (0 : ℝ)))
    (hVBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity
        (fun τ x => (actualHartreeTrueTwoStageScaledCore a c τ x : ℂ))
        (fun τ x => (dV τ x : ℂ)) r t rho|
          ≤ BV rho)
    (b w Z : ℝ → ℂ) (B : ℝ) (hB : 0 < B)
    (bdot wdot Zdot Sdot Pdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hbNorm : ‖b s‖ ≤ a s * B ^ 2)
    (hwNorm : ‖w s‖ ≤ a s * B ^ 2)
    (hDet : (a s) ^ 2 * B ^ 4 / 256 ≤ actualRealCramerDet (b s) (w s))
    (hS : HasDerivAt
      (fun t => actualMomentLockedScaledScaleSource (a t) (c t) r)
      Sdot s)
    (hP : HasDerivAt
      (fun t => actualMomentLockedScaledPhaseSource (a t) (c t) r)
      Pdot s) :
    ∃ Fdot : ℂ,
      HasDerivAt
        (fun t => actualHartreeLaplacianScaledKummerSource
          (a t) (ell t) (c t) (z t) r) Fdot s ∧
      ∃ pbDot pwDot : ℝ,
        let pb : ℝ → ℝ := fun t =>
          (actualRealCramerCorrection (b t) (w t) (Z t)).1
        let pw : ℝ → ℝ := fun t =>
          (actualRealCramerCorrection (b t) (w t) (Z t)).2
        HasDerivAt pb pbDot s ∧
        HasDerivAt pw pwDot s ∧
        |pbDot| + |pwDot| ≤
          1024 / (a s * B ^ 2) *
            ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ ∧
        HasDerivAt
          (fun t => actualHartreeTrueMovingAdjustedSource
            a ell c z b w Z t r)
          (-Fdot -
            ((pbDot : ℂ) *
                actualMomentLockedScaledScaleSource (a s) (c s) r +
              (pb s : ℂ) * Sdot) -
            ((pwDot : ℂ) *
                actualMomentLockedScaledPhaseSource (a s) (c s) r +
              (pw s : ℂ) * Pdot)) s := by
  have hRiesz : ∃ Fdot : ℂ,
      HasDerivAt
        (fun t => actualHartreeLaplacianScaledKummerSource
          (a t) (ell t) (c t) (z t) r) Fdot s :=
    ⟨_, actual_Hartree_original_Kummer_source_time_from_full_scaled_orbit
      a ell c z dV dZ r s adot hr hA ha I hI hs
      hV hZRe hZIm hZat
      hMixMeas hMixInt hMixDotMeas BM hBM hMixBound
      hZMeas hZInt hZDotMeas BZ hBZ hZBound
      hVMeas hVInt hVDotMeas BV hBV hVBound⟩
  obtain ⟨Fdot, hFdot⟩ := hRiesz
  have hFnegative : HasDerivAt
      (fun t => -actualHartreeLaplacianScaledKummerSource
        (a t) (ell t) (c t) (z t) r) (-Fdot) s := by
    convert hFdot.neg using 1 <;> (funext t; rfl)
  obtain ⟨pbDot, pwDot, hpb, hpw, hSpeed, hFull⟩ :=
    actual_Hartree_true_moving_adjusted_source_derivative
      a ell c z b w Z s r (a s) B ha hB
      bdot wdot Zdot (-Fdot) Sdot Pdot
      hb hw hZ hbNorm hwNorm hDet
      hFnegative hS hP
  exact ⟨Fdot, hFdot, pbDot, pwDot, hpb, hpw, hSpeed, hFull⟩

end HBL.TypeIIDynamicSelection
