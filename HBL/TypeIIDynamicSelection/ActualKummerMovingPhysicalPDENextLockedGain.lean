import HBL.TypeIIDynamicSelection.ActualKummerMovingTailTruePhysicalPDE
import HBL.TypeIIDynamicSelection.ActualKummerRepairTrueNonlinearSource
import HBL.TypeIIDynamicSelection.ActualHartreeLockedPhysicalGain
import Mathlib.Tactic

/-!
# Exact actual-Hartree moving-Kummer-tail PDE source with the locked gain

This is an analytical producer: the residual on the left is the ORIGINAL
renormalized PDE evaluated on the same time-dependent physical background
with and without the concrete moving outer repair. The full nonlinear
Hartree density (linear, quadratic, cubic and quartic in the repair) is
retained, and the true local cubic factor is controlled by radial physics.

The three-region gluing and finite iteration remain open; this theorem
does not assume a residual order label or postulate a PDE source estimate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_moving_Kummer_outer_repair_full_PDE_next_locked_gain
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z : ℝ → ℝ → ℂ)
    (b omega s r B A beta rhoStar rho CX CD : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : ContinuousAt a s) (hR : 0 < R)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hs : 1 ≤ s)
    (hbeta : 1 / 2 < beta)
    (_hrhoStar : 0 < rhoStar)
    (_hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell s ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius (ell s) ≤ a s * R)
    (hCX : 0 ≤ CX) (hXup : a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hCD : 0 ≤ CD)
    (hDtime : ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho))
    (hz : Measurable (z (time s)))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hsep : 2 * r ≤ a s * R) :
    let U : ℝ → ℝ → ℂ := fun t y =>
      (actualMomentLockedCore (c t) y : ℂ) +
        rescalePhysicalRadiation (ell t) (z (time t)) y
    let Ctime := actualKummerRepairTrueBackgroundTimeConstant B A CX CD
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A)
    let kl := actualHartreeLockedKappa beta rhoStar
    ‖complexRadialRenormalizedResidual
        (fun t y => U t y + actualKummerPhysicalOuterRepair a R p q t y)
        b omega s r -
      complexRadialRenormalizedResidual U b omega s r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ctime * M ^ 3) *
        s ^ (-(rho + kl)) := by
  dsimp only
  let U : ℝ → ℝ → ℂ := fun t y =>
    (actualMomentLockedCore (c t) y : ℂ) +
      rescalePhysicalRadiation (ell t) (z (time t)) y
  let Ctime := actualKummerRepairTrueBackgroundTimeConstant B A CX CD
  let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A)
  let kl := actualHartreeLockedKappa beta rhoStar
  let kc := actualKummerRepairCenterTimeGain beta
  have hExact :=
    actual_Kummer_moving_tail_actual_Hartree_core_PDE_source_exact
      a ell c time R p q z b omega s r B A
      ha haCont hR hell hellOne hc hB hA hr hsep
      hz hSup hStrauss
  dsimp only at hExact
  have hNL :=
    actual_Hartree_repair_full_nonlinear_PDE_source_sqrt_clock_gain
      (ell s) (a s) R B A (c s) s beta rho CX CD r
      hell hellOne (ha s) hR hB hA hc hs hbeta hrho
      htrap hXlow hCX hXup hCD (p s) (q s) hDtime
      (z (time s)) hz hSup hStrauss hr hrOne hsep
  dsimp only at hNL
  have hH : 0 ≤ Ctime := by
    have hMono : 0 ≤ 2 + 9 * monopoleRadialBoundConstant := by
      have hm := monopoleRadialBoundConstant_pos.le
      positivity
    have hRad : 0 ≤ 2 * (B + A) := by positivity
    dsimp [Ctime, actualKummerRepairTrueBackgroundTimeConstant]
    positivity
  have hM : 0 ≤ M := by
    have hm := monopoleRadialBoundConstant_pos.le
    dsimp [M]
    positivity
  have hCoef :
      0 ≤ 2 * (4 * Real.pi * hartreeKappa) * Ctime * M ^ 3 := by
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
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ctime * M ^ 3) *
          s ^ (-(rho + kc)) := by
      simpa only [U, Ctime, M, kc] using hNL
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ctime * M ^ 3) *
          s ^ (-(rho + kl)) :=
      mul_le_mul_of_nonneg_left hPow hCoef

end HBL.TypeIIDynamicSelection
