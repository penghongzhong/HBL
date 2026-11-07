import HBL.TypeIIDynamicSelection.ActualKummerTwoActualRepairPDELayer
import HBL.TypeIIDynamicSelection.ActualKummerMovingCorrectedPhysicalPDENextLockedGain
import HBL.FiniteProfileResidualLedger
import Mathlib.Tactic

/-!
# Finite list of genuinely realized moving physical Kummer tail fields

A prior correction need not be an abstract field with an assumed bubble
envelope: it can be the finite sum of the ACTUAL compact moving Kummer
replacements, each with the genuine physical sqrt-clock shell bound and
the selected physical value/slope jet estimate.

The finite sum is measurable and satisfies a global bubble bound with the
explicit sum of the single-tail constants. We then apply the ORIGINAL
nonlocal Hartree PDE residual identity to the next moving repair against
this finite *actual* corrected profile, obtaining its locked next-layer
order without inserting an independent current-background envelope.

This verifies the Kummer-tail part of the finite recursion. It does NOT
assert that every physical inner and remote source is one of these tails,
nor does it prove the whole order-9/4 parametrix or Type-II blowup orbit.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual physical moving Kummer tail along one selected trajectory.
Its size, rather than an abstract generated order tag, is the verified
value/slope jet, normalized radius and sqrt-clock inequality. -/
structure ActualKummerPhysicalRepairTrajectory where
  a : ℝ → ℝ
  R : ℝ
  p q : ℝ → ℂ
  rho CX CD : ℝ
  Rpos : 0 < R
  apos : ∀ s : ℝ, 1 ≤ s → 0 < a s
  rho_half : (1 / 2 : ℝ) ≤ rho
  CX_nonneg : 0 ≤ CX
  CD_nonneg : 0 ≤ CD
  radius : ∀ s : ℝ, 1 ≤ s →
    a s * R ≤ CX * s ^ (1 / 2 : ℝ)
  jet : ∀ s : ℝ, 1 ≤ s →
    ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho)

/-- Actual physical Kummer fields, not a collection of formal source tags. -/
def actualKummerFinitePhysicalTail
    (packets : List ActualKummerPhysicalRepairTrajectory)
    (s y : ℝ) : ℂ :=
  (packets.map (fun P =>
    actualKummerPhysicalOuterRepair P.a P.R P.p P.q s y)).sum

def actualKummerFinitePhysicalTailConstant
    (packets : List ActualKummerPhysicalRepairTrajectory) : ℝ :=
  (packets.map (fun P => (1 + 2 * P.CX) * P.CD)).sum

theorem actual_Kummer_finite_physical_tail_constant_nonneg
    (packets : List ActualKummerPhysicalRepairTrajectory) :
    0 ≤ actualKummerFinitePhysicalTailConstant packets := by
  induction packets with
  | nil =>
      simp [actualKummerFinitePhysicalTailConstant]
  | cons P packets ih =>
      simp only [actualKummerFinitePhysicalTailConstant,
        List.map_cons, List.sum_cons] at ih ⊢
      have hP : 0 ≤ (1 + 2 * P.CX) * P.CD := by
        have hCX := P.CX_nonneg
        have hCD := P.CD_nonneg
        positivity
      exact add_nonneg hP ih

/-- The true current finite Kummer correction is a bona fide measurable
complex spatial field, including all compact moving shells. -/
theorem actual_Kummer_finite_physical_tail_measurable
    (packets : List ActualKummerPhysicalRepairTrajectory)
    (s : ℝ) (hs : 1 ≤ s) :
    Measurable (actualKummerFinitePhysicalTail packets s) := by
  induction packets with
  | nil =>
      simpa [actualKummerFinitePhysicalTail] using
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))
  | cons P packets ih =>
      have hP :
          Measurable (actualKummerPhysicalOuterRepair
            P.a P.R P.p P.q s) :=
        actual_Kummer_physical_outer_repair_measurable
          P.a P.R P.p P.q s (P.apos s hs).ne' P.Rpos.ne'
      change Measurable (fun y =>
        actualKummerPhysicalOuterRepair P.a P.R P.p P.q s y +
          actualKummerFinitePhysicalTail packets s y)
      exact hP.add ih

/-- Exact finite-list bubble envelope; no uniform spatial bound is assumed
for the sum of physical tails. -/
theorem actual_Kummer_finite_physical_tail_bubble_envelope
    (packets : List ActualKummerPhysicalRepairTrajectory)
    (s : ℝ) (hs : 1 ≤ s) :
    ∀ y : ℝ, 0 < y →
      ‖actualKummerFinitePhysicalTail packets s y‖ ≤
        actualKummerFinitePhysicalTailConstant packets * bubble y := by
  induction packets with
  | nil =>
      intro y hy
      simp [actualKummerFinitePhysicalTail,
        actualKummerFinitePhysicalTailConstant]
  | cons P packets ih =>
      intro y hy
      have hP :=
        actual_Kummer_physical_outer_repair_bubble_from_clock
          P.a P.R P.p P.q s P.rho P.CX P.CD
          (P.apos s hs) P.Rpos hs P.rho_half
          P.CX_nonneg P.CD_nonneg
          (P.radius s hs) (P.jet s hs) y hy
      have hRest := ih y hy
      calc
        ‖actualKummerFinitePhysicalTail (P :: packets) s y‖ =
            ‖actualKummerPhysicalOuterRepair P.a P.R P.p P.q s y +
              actualKummerFinitePhysicalTail packets s y‖ := rfl
        _ ≤ ‖actualKummerPhysicalOuterRepair
                P.a P.R P.p P.q s y‖ +
              ‖actualKummerFinitePhysicalTail packets s y‖ :=
          norm_add_le _ _
        _ ≤ ((1 + 2 * P.CX) * P.CD) * bubble y +
              actualKummerFinitePhysicalTailConstant packets *
                bubble y :=
          add_le_add hP hRest
        _ = actualKummerFinitePhysicalTailConstant (P :: packets) *
              bubble y := by
          simp only [actualKummerFinitePhysicalTailConstant,
            List.map_cons, List.sum_cons]
          ring

/-- The next actual moving Kummer replacement has a genuine locked
full-nonlinear-Hartree PDE residual on the background obtained from any
finite number of preceding actual physical tail corrections. -/
theorem actual_Hartree_next_Kummer_after_finite_actual_repairs_PDE_gain
    (packets : List ActualKummerPhysicalRepairTrajectory)
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
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell s ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius (ell s) ≤ a s * R)
    (hCX : 0 ≤ CX) (hXup : a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hCD : 0 ≤ CD)
    (hJet : ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho))
    (hz : Measurable (z (time s)))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hsep : 2 * r ≤ a s * R) :
    let H := actualKummerFinitePhysicalTail packets
    let CH := actualKummerFinitePhysicalTailConstant packets
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
  let H : ℝ → ℝ → ℂ := actualKummerFinitePhysicalTail packets
  let CH := actualKummerFinitePhysicalTailConstant packets
  have hCH : 0 ≤ CH :=
    actual_Kummer_finite_physical_tail_constant_nonneg packets
  have hHmeas : Measurable (H s) :=
    actual_Kummer_finite_physical_tail_measurable packets s hs
  have hH :
      ∀ y : ℝ, 0 < y → ‖H s y‖ ≤ CH * bubble y :=
    actual_Kummer_finite_physical_tail_bubble_envelope packets s hs
  have hRaw :=
    actual_Hartree_moving_corrected_Kummer_full_PDE_next_locked_gain
      a ell c time R p q z H b omega s r B A CH
      beta rhoStar rho CX CD
      ha haCont hR hell hellOne hc hB hA hCH
      hs hbeta hrhoStar hflat hrho htrap hXlow hCX hXup
      hCD hJet hz hHmeas hSup hStrauss hH
      hr hrOne hsep
  dsimp only at hRaw
  simpa only [H, CH] using hRaw

end HBL.TypeIIDynamicSelection
