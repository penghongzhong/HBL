import HBL.TypeIIDynamicSelection.ActualKummerRepairBubbleEnvelopeFromClock
import HBL.TypeIIDynamicSelection.ActualKummerMovingCorrectedPDENextLockedGain
import Mathlib.Tactic

/-!
# Two successive actual moving Kummer repairs: nonlinear Hartree core source

This is the first source-faithful two-step test of the finite HBL recursion.
The previous correction H is not arbitrary: it is exactly the preceding
physical Kummer replacement with its original boundary value and slope.
The bubble envelope required for the nonlinear next-step Hartree estimate
is proved from the previous repair's actual jet and physical sqrt clock,
and its measurability is proved from the concrete compact shell support.

The next moving repair's full nonlinear Hartree PDE residual therefore
gains rho + kappa_locked on this explicitly corrected background. All
local cubic and quartic-density cross terms are retained.

This certifies the INNER-CORE residual produced by two actual shells. The
remaining interior/remote fields, physical C1 gluing and the full global
9/4 parametrix still have to be constructed; the indicator-defined tail
alone is not a globally C1 profile.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original moving Kummer replacement is a concrete measurable
complex radial function at each positive physical shell time. -/
theorem actual_Kummer_physical_outer_repair_measurable
    (a : ℝ → ℝ) (R : ℝ) (p q : ℝ → ℂ)
    (s : ℝ) (ha : a s ≠ 0) (hR : R ≠ 0) :
    Measurable (actualKummerPhysicalOuterRepair a R p q s) := by
  have hContinuous :
      Continuous (actualKummerPhysicalInterfaceRepair
        (a s) R (p s) (q s)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (actual_Kummer_physical_interface_repair_derivatives
      (a s) R y ha hR (p s) (q s)).1.continuousAt
  change Measurable
    ((Ioc (a s * R) (2 * a s * R)).indicator
      (actualKummerPhysicalInterfaceRepair (a s) R (p s) (q s)))
  exact hContinuous.measurable.indicator measurableSet_Ioc

/-- The second ACTUAL Kummer repair's original Hartree PDE residual is
small on the true physical core, against a background already corrected by
the FIRST ACTUAL moving Kummer replacement, with no separate source-order
or spatial-envelope premise for that first correction. -/
theorem actual_Hartree_two_successive_Kummer_repairs_core_PDE_next_locked_gain
    (a0 a1 ell c time : ℝ → ℝ)
    (R0 R1 : ℝ)
    (p0 q0 p1 q1 : ℝ → ℂ) (z : ℝ → ℝ → ℂ)
    (b omega s r B A beta rhoStar rho0 rho1
       CX0 CD0 CX1 CD1 : ℝ)
    (ha0 : 0 < a0 s) (hR0 : 0 < R0)
    (ha1 : ∀ t : ℝ, 0 < a1 t)
    (ha1Cont : ContinuousAt a1 s) (hR1 : 0 < R1)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hs : 1 ≤ s)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho0 : (1 / 2 : ℝ) ≤ rho0)
    (hrho1 : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho1)
    (htrap : ell s ≤ s ^ (-beta))
    (hCX0 : 0 ≤ CX0) (hCD0 : 0 ≤ CD0)
    (hX0 : a0 s * R0 ≤ CX0 * s ^ (1 / 2 : ℝ))
    (hJet0 : ‖p0 s‖ + R0 * ‖q0 s‖ ≤ CD0 * s ^ (-rho0))
    (hXlow1 : actualHartreeSlowInnerRadius (ell s) ≤ a1 s * R1)
    (hCX1 : 0 ≤ CX1)
    (hXup1 : a1 s * R1 ≤ CX1 * s ^ (1 / 2 : ℝ))
    (hCD1 : 0 ≤ CD1)
    (hJet1 : ‖p1 s‖ + R1 * ‖q1 s‖ ≤ CD1 * s ^ (-rho1))
    (hz : Measurable (z (time s)))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hsep : 2 * r ≤ a1 s * R1) :
    let CH := (1 + 2 * CX0) * CD0
    let U : ℝ → ℝ → ℂ := fun t y =>
      (actualMomentLockedCore (c t) y : ℂ) +
        rescalePhysicalRadiation (ell t) (z (time t)) y +
        actualKummerPhysicalOuterRepair a0 R0 p0 q0 t y
    let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX1 CD1
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
    let kl := actualHartreeLockedKappa beta rhoStar
    ‖complexRadialRenormalizedResidual
        (fun t y => U t y +
          actualKummerPhysicalOuterRepair a1 R1 p1 q1 t y)
        b omega s r -
      complexRadialRenormalizedResidual U b omega s r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
        s ^ (-(rho1 + kl)) := by
  dsimp only
  let CH : ℝ := (1 + 2 * CX0) * CD0
  let H : ℝ → ℝ → ℂ := actualKummerPhysicalOuterRepair a0 R0 p0 q0
  have hCH : 0 ≤ CH := by dsimp [CH]; positivity
  have hHmeas : Measurable (H s) :=
    actual_Kummer_physical_outer_repair_measurable
      a0 R0 p0 q0 s ha0.ne' hR0.ne'
  have hHCorr : ∀ u : ℝ, 0 < u →
      ‖H s u‖ ≤ CH * bubble u := by
    simpa only [H, CH] using
      actual_Kummer_physical_outer_repair_bubble_from_clock
        a0 R0 p0 q0 s rho0 CX0 CD0
        ha0 hR0 hs hrho0 hCX0 hCD0 hX0 hJet0
  have hSource :=
    actual_Hartree_moving_Kummer_corrected_outer_full_PDE_next_locked_gain
      a1 ell c time R1 p1 q1 z H b omega s r
      B A CH beta rhoStar rho1 CX1 CD1
      ha1 ha1Cont hR1 hell hellOne hc hB hA hCH
      hs hbeta hrhoStar hflat hrho1 htrap
      hXlow1 hCX1 hXup1 hCD1 hJet1
      hz hHmeas hSup hStrauss hHCorr
      hr hrOne hsep
  dsimp only at hSource
  simpa only [H, CH] using hSource

end HBL.TypeIIDynamicSelection
