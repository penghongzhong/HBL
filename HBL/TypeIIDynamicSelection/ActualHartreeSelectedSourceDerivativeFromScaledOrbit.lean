import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingOriginalSourceFromScaledOrbit
import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import Mathlib.Tactic

/-!
# True Cramer-selected Hartree source: time derivative from the physical scaled orbit

This composes the original critically scaled quartic Riesz-interaction
identity and its exact time derivative with the actual real two-speed
Cramer differentiation. The temporal derivative of the original Hartree
forcing is thereby DERIVED, rather than separately assumed.

The remaining scaled-orbit regularity and its quantitative bounds must
still be obtained from the same original nonlocal PDE trajectory.
This theorem does not assert time-positive four-region error or Type-II
blowup rate; no independent modulation derivative is assumed.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- On one genuinely scaled nonlocal Hartree orbit, produce the complete
time derivative of the Cramer-selected physical Kummer source from the
fixed-observer critical Riesz interaction. Both speed derivatives are
outputs of the original real Cramer determinant theorem. -/
theorem actual_Hartree_true_selected_source_derivative_from_scaled_orbit
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s r adot alpha B : ℝ)
    (ha : 0 < a s) (halpha : 0 < alpha) (hB : 0 < B)
    (hA : HasDerivAt a adot s)
    (bdot wdot Zdot scaledDot Sdot Pdot : ℂ)
    (hScaled : HasDerivAt
      (fun t => actualHartreeTrueCriticallyScaledOriginalInteraction
        a ell c z t r) scaledDot s)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hbNorm : ‖b s‖ ≤ alpha * B ^ 2)
    (hwNorm : ‖w s‖ ≤ alpha * B ^ 2)
    (hdet : alpha ^ 2 * B ^ 4 / 256 ≤
      actualRealCramerDet (b s) (w s))
    (hS : HasDerivAt
      (fun t => actualMomentLockedScaledScaleSource (a t) (c t) r)
      Sdot s)
    (hP : HasDerivAt
      (fun t => actualMomentLockedScaledPhaseSource (a t) (c t) r)
      Pdot s) :
    let Fdot : ℂ :=
      - (-( ((adot / (2 * Real.sqrt (a s)) : ℝ) : ℂ) /
            (((Real.sqrt (a s) : ℝ) : ℂ) ^ 2)) *
          actualHartreeTrueCriticallyScaledOriginalInteraction
            a ell c z s r +
        (((Real.sqrt (a s) : ℝ) : ℂ)⁻¹) * scaledDot)
    ∃ pbDot pwDot : ℝ,
      let pb : ℝ → ℝ := fun t =>
        (actualRealCramerCorrection (b t) (w t) (Z t)).1
      let pw : ℝ → ℝ := fun t =>
        (actualRealCramerCorrection (b t) (w t) (Z t)).2
      HasDerivAt pb pbDot s ∧
      HasDerivAt pw pwDot s ∧
      |pbDot| + |pwDot| ≤
        1024 / (alpha * B ^ 2) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ ∧
      HasDerivAt
        (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t r)
        (Fdot -
          ((pbDot : ℂ) *
              actualMomentLockedScaledScaleSource (a s) (c s) r +
            (pb s : ℂ) * Sdot) -
          ((pwDot : ℂ) *
              actualMomentLockedScaledPhaseSource (a s) (c s) r +
            (pw s : ℂ) * Pdot)) s := by
  let Fdot : ℂ :=
    - (-( ((adot / (2 * Real.sqrt (a s)) : ℝ) : ℂ) /
          (((Real.sqrt (a s) : ℝ) : ℂ) ^ 2)) *
        actualHartreeTrueCriticallyScaledOriginalInteraction a ell c z s r +
      (((Real.sqrt (a s) : ℝ) : ℂ)⁻¹) * scaledDot)
  have hPhysical0 :=
    actual_Hartree_original_moving_source_derivative_from_scaled_orbit
      a ell c z s r adot hA ha scaledDot hScaled
  have hF : HasDerivAt
      (fun t => -actualHartreeLaplacianScaledKummerSource
        (a t) (ell t) (c t) (z t) r) Fdot s := by
    simpa only [Fdot, Pi.neg_apply] using hPhysical0.neg
  exact actual_Hartree_true_moving_adjusted_source_derivative
    a ell c z b w Z s r alpha B halpha hB
    bdot wdot Zdot Fdot Sdot Pdot
    hb hw hZ hbNorm hwNorm hdet hF hS hP

end HBL.TypeIIDynamicSelection
