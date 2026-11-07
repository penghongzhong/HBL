import HBL.TypeIIDynamicSelection.ActualKummerMovingCorrectedBackgroundPDE
import HBL.TypeIIDynamicSelection.ActualKummerRepairCorrectedNonlinearSource
import HBL.TypeIIDynamicSelection.ActualHartreeLockedPhysicalGain
import Mathlib.Tactic

/-!
# Genuine next-layer Hartree PDE source on the corrected physical background

The actual moving Kummer outer repair is evaluated against V_c + Z_ell + H,
where H is a genuine previous correction with a quantitative bubble envelope.
The FULL quartic-density Hartree feedback and its TRUE corrected local cubic
are controlled after the original PDE residual identity.

This is a legitimate nonlinear iteration producer. No proxy cubic, assigned
source-order label, guessed remote trace or Type-II rate enters the proof.
The complete finite physical 9/4 profile still requires iteration and
three-region source/energy matching.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_moving_Kummer_corrected_outer_full_PDE_next_locked_gain
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z H : ℝ → ℝ → ℂ)
    (b omega s r B A CH beta rhoStar rho CX CD : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : ContinuousAt a s) (hR : 0 < R)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hs : 1 ≤ s)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell s ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius (ell s) ≤ a s * R)
    (hCX : 0 ≤ CX) (hXup : a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hCD : 0 ≤ CD)
    (hDtime : ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho))
    (hz : Measurable (z (time s)))
    (hHmeas : Measurable (H s))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hHCorr : ∀ u : ℝ, 0 < u → ‖H s u‖ ≤ CH * bubble u)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hsep : 2 * r ≤ a s * R) :
    let U : ℝ → ℝ → ℂ := fun t y =>
      (actualMomentLockedCore (c t) y : ℂ) +
        rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
    let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX CD
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
    let kl := actualHartreeLockedKappa beta rhoStar
    ‖complexRadialRenormalizedResidual
        (fun t y => U t y + actualKummerPhysicalOuterRepair a R p q t y)
        b omega s r -
      complexRadialRenormalizedResidual U b omega s r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
        s ^ (-(rho + kl)) := by
  dsimp only
  let U : ℝ → ℝ → ℂ := fun t y =>
    (actualMomentLockedCore (c t) y : ℂ) +
      rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
  let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX CD
  let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
  let kl := actualHartreeLockedKappa beta rhoStar
  let kc := actualKummerRepairCenterTimeGain beta
  have hExact :=
    actual_Kummer_moving_repair_corrected_Hartree_core_PDE_exact
      a ell c time R p q z H b omega s r B A CH
      ha haCont hR hell hellOne hc hB hA hCH hr hsep
      hz hHmeas hSup hStrauss hHCorr
  dsimp only at hExact
  have hNL :=
    actual_Hartree_Kummer_corrected_full_nonlinear_source_time_gain
      (ell s) (a s) R B A CH (c s) s beta rho CX CD r
      hell hellOne (ha s) hR hB hA hCH hc hs hbeta hrho
      htrap hXlow hCX hXup hCD (p s) (q s) hDtime
      (z (time s)) (H s) hz hHmeas hSup hStrauss hHCorr
      hr hrOne hsep
  dsimp only at hNL
  have hMono : 0 ≤ monopoleRadialBoundConstant :=
    monopoleRadialBoundConstant_pos.le
  have hCt : 0 ≤ Ct := by
    dsimp [Ct, actualKummerRepairCorrectedTimeConstant]
    positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hCoef :
      0 ≤ 2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3 := by
    unfold hartreeKappa
    positivity
  have hK : kl ≤ kc :=
    actual_Hartree_locked_kappa_le_repair beta rhoStar
  have hPow : s ^ (-(rho + kc)) ≤ s ^ (-(rho + kl)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  calc
    _ = ‖(radialHartreeExteriorPotential
          (actualKummerPhysicalRepairOuterDensityDifference
            (U s) (a s) R (p s) (q s)) (a s * R) r : ℂ) *
            actualWholeRadiationLocalCubic (U s) r‖ := by
      rw [hExact]
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
          s ^ (-(rho + kc)) := by
      simpa only [U, Ct, M, kc] using hNL
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
          s ^ (-(rho + kl)) :=
      mul_le_mul_of_nonneg_left hPow hCoef

end HBL.TypeIIDynamicSelection
