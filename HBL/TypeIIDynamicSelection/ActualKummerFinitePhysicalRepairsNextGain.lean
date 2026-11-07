import HBL.TypeIIDynamicSelection.ActualKummerTwoActualRepairPDELayer
import HBL.TypeIIDynamicSelection.ActualKummerMovingCorrectedPDENextLockedGain
import Mathlib.Tactic

/-!
# Finite sum of ACTUAL Kummer repairs feeds the next nonlinear Hartree layer

Every shell packet stores the actual Kummer interface repair field, its
moving physical shell, its original value/slope jet and the sqrt-clock
radius bound at a common physical time s. No abstract linear regional
solver and no assigned generated-source order are used.

The finite sum has a proved global bubble envelope and genuine
measurability, allowing the complete nonlocal quartic Hartree PDE source
of the NEXT moving repair to be estimated on that corrected background.

This is a genuine finite Kummer-subchain of HBL 2.13, but the full
three-region profile still requires real inner/remote corrections,
their PDE source estimates and physical global energy gluing.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Honest physical Kummer repair at a fixed common renormalized time.
The quantitative shell/jet estimates are the same hypotheses already
produced by the source-selected upper jet and exact physical clock. -/
structure ActualKummerPhysicalShellPacket (s : ℝ) where
  a : ℝ → ℝ
  R : ℝ
  p : ℝ → ℂ
  q : ℝ → ℂ
  rho : ℝ
  CX : ℝ
  CD : ℝ
  a_pos : 0 < a s
  R_pos : 0 < R
  rho_half : (1 / 2 : ℝ) ≤ rho
  CX_nonneg : 0 ≤ CX
  CD_nonneg : 0 ≤ CD
  radius_bound : a s * R ≤ CX * s ^ (1 / 2 : ℝ)
  jet_bound : ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho)

/-- The correction is the actual compact physical replacement field,
not an assigned source or an arbitrary function of a stated order. -/
def actualKummerPhysicalPacketTail {s : ℝ}
    (P : ActualKummerPhysicalShellPacket s) (t y : ℝ) : ℂ :=
  actualKummerPhysicalOuterRepair P.a P.R P.p P.q t y

/-- Literal finite sum of the physical moving Kummer repair fields. -/
def actualKummerFinitePhysicalTail {s : ℝ}
    (packets : List (ActualKummerPhysicalShellPacket s)) (t y : ℝ) : ℂ :=
  (packets.map (fun P => actualKummerPhysicalPacketTail P t y)).sum

/-- Realized common physical bubble envelope for that literal finite sum. -/
def actualKummerFinitePhysicalTailConstant {s : ℝ}
    (packets : List (ActualKummerPhysicalShellPacket s)) : ℝ :=
  (packets.map (fun P => (1 + 2 * P.CX) * P.CD)).sum

theorem actual_Kummer_finite_physical_tail_constant_nonneg
    {s : ℝ} (packets : List (ActualKummerPhysicalShellPacket s)) :
    0 ≤ actualKummerFinitePhysicalTailConstant packets := by
  induction packets with
  | nil => simp [actualKummerFinitePhysicalTailConstant]
  | cons P ps ih =>
      change 0 ≤
        (1 + 2 * P.CX) * P.CD +
          actualKummerFinitePhysicalTailConstant ps
      have hp : 0 ≤ (1 + 2 * P.CX) * P.CD := by
        have hc := P.CX_nonneg
        have hd := P.CD_nonneg
        positivity
      exact add_nonneg hp ih

/-- All previous ACTUAL Kummer tails are in the same physical bubble
class: the constant is computed from the original finite shell packets. -/
theorem actual_Kummer_finite_physical_tail_bubble_bound
    (s : ℝ) (hs : 1 ≤ s)
    (packets : List (ActualKummerPhysicalShellPacket s))
    (y : ℝ) (hy : 0 < y) :
    ‖actualKummerFinitePhysicalTail packets s y‖ ≤
      actualKummerFinitePhysicalTailConstant packets * bubble y := by
  induction packets with
  | nil =>
      simp [actualKummerFinitePhysicalTail,
        actualKummerFinitePhysicalTailConstant]
  | cons P ps ih =>
      have hP :=
        actual_Kummer_physical_outer_repair_bubble_from_clock
          P.a P.R P.p P.q s P.rho P.CX P.CD
          P.a_pos P.R_pos hs P.rho_half P.CX_nonneg P.CD_nonneg
          P.radius_bound P.jet_bound y hy
      have hOne :
          ‖actualKummerPhysicalPacketTail P s y‖ ≤
            ((1 + 2 * P.CX) * P.CD) * bubble y := by
        simpa only [actualKummerPhysicalPacketTail] using hP
      change
        ‖actualKummerPhysicalPacketTail P s y +
          actualKummerFinitePhysicalTail ps s y‖ ≤
        ((1 + 2 * P.CX) * P.CD +
          actualKummerFinitePhysicalTailConstant ps) * bubble y
      calc
        _ ≤ ‖actualKummerPhysicalPacketTail P s y‖ +
            ‖actualKummerFinitePhysicalTail ps s y‖ :=
          norm_add_le _ _
        _ ≤ ((1 + 2 * P.CX) * P.CD) * bubble y +
            actualKummerFinitePhysicalTailConstant ps * bubble y :=
          add_le_add hOne ih
        _ = ((1 + 2 * P.CX) * P.CD +
            actualKummerFinitePhysicalTailConstant ps) * bubble y := by ring

/-- Actual finite physical Kummer sum is measurable at the shared time;
no 'measurability of an arbitrary previous correction' is introduced. -/
theorem actual_Kummer_finite_physical_tail_measurable
    (s : ℝ) (packets : List (ActualKummerPhysicalShellPacket s)) :
    Measurable (actualKummerFinitePhysicalTail packets s) := by
  induction packets with
  | nil =>
      change Measurable (fun _ : ℝ => (0 : ℂ))
      exact measurable_const
  | cons P ps ih =>
      change Measurable (fun y =>
        actualKummerPhysicalPacketTail P s y +
          actualKummerFinitePhysicalTail ps s y)
      have hP : Measurable (actualKummerPhysicalPacketTail P s) :=
        actual_Kummer_physical_outer_repair_measurable
          P.a P.R P.p P.q s P.a_pos.ne' P.R_pos.ne'
      exact hP.add ih

/-- New genuine moving Kummer PDE source on the sum of finitely many
previous real physical Kummer tails: the nonlinear correction envelope
and measurability are DERIVED from their actual fields and clock bounds.
This is an inner-core physical source lemma, not a complete global C1
parametrix or a finished 2.13 theorem. -/
theorem actual_Hartree_finite_prior_Kummer_repairs_next_PDE_locked_gain
    (s : ℝ) (hs : 1 ≤ s)
    (packets : List (ActualKummerPhysicalShellPacket s))
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z : ℝ → ℝ → ℂ)
    (b omega r B A beta rhoStar rho CX CD : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : ContinuousAt a s) (hR : 0 < R)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
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
    let H : ℝ → ℝ → ℂ := actualKummerFinitePhysicalTail packets
    let CH := actualKummerFinitePhysicalTailConstant packets
    let U : ℝ → ℝ → ℂ := fun t y =>
      (actualMomentLockedCore (c t) y : ℂ) +
        rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
    let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX CD
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
    let kl := actualHartreeLockedKappa beta rhoStar
    ‖complexRadialRenormalizedResidual
        (fun t y => U t y + actualKummerPhysicalOuterRepair a R p q t y)
        (b s) (omega s) s r -
      complexRadialRenormalizedResidual U (b s) (omega s) s r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
        s ^ (-(rho + kl)) := by
  dsimp only
  let H : ℝ → ℝ → ℂ := actualKummerFinitePhysicalTail packets
  let CH : ℝ := actualKummerFinitePhysicalTailConstant packets
  have hCH : 0 ≤ CH := by
    dsimp [CH]
    exact actual_Kummer_finite_physical_tail_constant_nonneg packets
  have hHmeas : Measurable (H s) :=
    actual_Kummer_finite_physical_tail_measurable s packets
  have hHCorr : ∀ u : ℝ, 0 < u → ‖H s u‖ ≤ CH * bubble u := by
    intro u hu
    simpa only [H, CH] using
      actual_Kummer_finite_physical_tail_bubble_bound s hs packets u hu
  have hNext :=
    actual_Hartree_moving_Kummer_corrected_outer_full_PDE_next_locked_gain
      a ell c time R p q z H (b s) (omega s) s r
      B A CH beta rhoStar rho CX CD
      ha haCont hR hell hellOne hc hB hA hCH
      hs hbeta hrhoStar hflat hrho htrap
      hXlow hCX hXup hCD hJet
      hz hHmeas hSup hStrauss hHCorr
      hr hrOne hsep
  dsimp only at hNext
  simpa only [H, CH] using hNext

end HBL.TypeIIDynamicSelection
