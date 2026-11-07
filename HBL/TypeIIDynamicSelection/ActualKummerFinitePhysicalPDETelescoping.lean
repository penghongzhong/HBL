import HBL.TypeIIDynamicSelection.ActualKummerFinitePhysicalRepairsNextGain
import HBL.TypeIIDynamicSelection.ActualHartreeLockedPhysicalGain
import Mathlib.Tactic

/-!
# Exact nonlinear PDE telescoping and finite physical Kummer residual gain

No nonlinear superposition principle is used. For the actual Hartree
renormalized operator, the residual of Vc+Z+sum_i H_i minus that of Vc+Z
is exactly the telescoping sum of the original PDE residual differences.
Each increment is evaluated against the actual later-tail background.

The previous Kummer tails are literal compact physical replacements
constructed from their moving radius and exact value/slope jets. Each next
increment is estimated by the already verified genuine full-Hartree PDE
producer on the finite physical tail background, including nonlocal density
and local cubic interactions. This is a strict inner-core finite-source
certificate, NOT the full three-region 9/4 parametrix or a blowup orbit.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The same original moment-locked physical core plus real Hartree
radiation appearing in every actual Kummer packet. -/
def actualKummerFinitePhysicalBase
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (t y : ℝ) : ℂ :=
  (actualMomentLockedCore (c t) y : ℂ) +
    rescalePhysicalRadiation (ell t) (z (time t)) y

/-- Difference of two ACTUAL nonlinear Hartree PDE residuals, with the
literal finite moving Kummer correction inserted in the first one. -/
def actualKummerFinitePhysicalPDEGap {s : ℝ}
    (packets : List (ActualKummerPhysicalShellPacket s))
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
    (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
      actualKummerFinitePhysicalTail packets t y) b omega s r -
  complexRadialRenormalizedResidual
    (actualKummerFinitePhysicalBase ell c time z) b omega s r

/-- Exact sum of genuine *successive* nonlinear PDE differences, not the
sum of synthetic linearized source terms. -/
def actualKummerFinitePhysicalPDEIncrements {s : ℝ}
    (packets : List (ActualKummerPhysicalShellPacket s))
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega r : ℝ) : ℂ :=
  match packets with
  | [] => 0
  | P :: ps =>
      (complexRadialRenormalizedResidual
        (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
          actualKummerFinitePhysicalTail ps t y +
          actualKummerPhysicalPacketTail P t y) b omega s r -
        complexRadialRenormalizedResidual
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail ps t y) b omega s r) +
      actualKummerFinitePhysicalPDEIncrements ps ell c time z b omega r

/-- Algebraic decomposition remains valid for the fully nonlinear
nonlocal Hartree operator because it is a telescoping difference of
complete PDE residuals, not a claim of linearity of that operator. -/
theorem actual_Kummer_finite_real_PDE_residual_telescopes
    {s : ℝ} (packets : List (ActualKummerPhysicalShellPacket s))
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega r : ℝ) :
    actualKummerFinitePhysicalPDEGap packets ell c time z b omega r =
      actualKummerFinitePhysicalPDEIncrements packets
        ell c time z b omega r := by
  induction packets with
  | nil =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail ([] :
              List (ActualKummerPhysicalShellPacket s)) t y) =
          actualKummerFinitePhysicalBase ell c time z := by
        funext t y
        simp [actualKummerFinitePhysicalTail]
      simp only [actualKummerFinitePhysicalPDEGap,
        actualKummerFinitePhysicalPDEIncrements, hEq, sub_self]
  | cons P ps ih =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail (P :: ps) t y) =
          (fun t y =>
            actualKummerFinitePhysicalBase ell c time z t y +
              actualKummerFinitePhysicalTail ps t y +
              actualKummerPhysicalPacketTail P t y) := by
        funext t y
        change actualKummerFinitePhysicalBase ell c time z t y +
          (actualKummerPhysicalPacketTail P t y +
            actualKummerFinitePhysicalTail ps t y) =
          actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail ps t y +
              actualKummerPhysicalPacketTail P t y
        abel
      have hSplit :
          actualKummerFinitePhysicalPDEGap (P :: ps)
              ell c time z b omega r =
            (complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualKummerFinitePhysicalTail ps t y +
                actualKummerPhysicalPacketTail P t y) b omega s r -
              complexRadialRenormalizedResidual
                (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                  actualKummerFinitePhysicalTail ps t y) b omega s r) +
            actualKummerFinitePhysicalPDEGap ps ell c time z b omega r := by
        unfold actualKummerFinitePhysicalPDEGap
        rw [hEq]
        ring
      rw [hSplit, ih]
      rfl

/-- Explicit sum of constants generated from the genuine full-Hartree
finite-tail background and its same-current-orbit nonlinear source. -/
def actualKummerFinitePhysicalPDEConstant {s : ℝ}
    (packets : List (ActualKummerPhysicalShellPacket s))
    (B A : ℝ) : ℝ :=
  match packets with
  | [] => 0
  | P :: ps =>
      let CH := actualKummerFinitePhysicalTailConstant ps
      let Ct := actualKummerRepairCorrectedTimeConstant B A CH P.CX P.CD
      let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
      (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) +
        actualKummerFinitePhysicalPDEConstant ps B A

theorem actual_Kummer_finite_physical_PDE_constant_nonneg
    {s : ℝ} (packets : List (ActualKummerPhysicalShellPacket s))
    (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    0 ≤ actualKummerFinitePhysicalPDEConstant packets B A := by
  induction packets with
  | nil =>
      simp [actualKummerFinitePhysicalPDEConstant]
  | cons P ps ih =>
      have hCH : 0 ≤ actualKummerFinitePhysicalTailConstant ps :=
        actual_Kummer_finite_physical_tail_constant_nonneg ps
      have hM : 0 ≤
          2 + 9 * monopoleRadialBoundConstant +
            2 * (B + A) + actualKummerFinitePhysicalTailConstant ps := by
        have hm := monopoleRadialBoundConstant_pos.le
        positivity
      have hCt : 0 ≤ actualKummerRepairCorrectedTimeConstant
          B A (actualKummerFinitePhysicalTailConstant ps) P.CX P.CD := by
        dsimp [actualKummerRepairCorrectedTimeConstant]
        have hm := monopoleRadialBoundConstant_pos.le
        have hCX := P.CX_nonneg
        have hCD := P.CD_nonneg
        positivity
      change 0 ≤
        2 * (4 * Real.pi * hartreeKappa) *
            actualKummerRepairCorrectedTimeConstant
              B A (actualKummerFinitePhysicalTailConstant ps) P.CX P.CD *
            (2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) +
              actualKummerFinitePhysicalTailConstant ps) ^ 3 +
          actualKummerFinitePhysicalPDEConstant ps B A
      have hCoeff : 0 ≤
        2 * (4 * Real.pi * hartreeKappa) *
            actualKummerRepairCorrectedTimeConstant
              B A (actualKummerFinitePhysicalTailConstant ps) P.CX P.CD *
            (2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) +
              actualKummerFinitePhysicalTailConstant ps) ^ 3 := by
        unfold hartreeKappa
        positivity
      exact add_nonneg hCoeff ih

/-- All genuine Kummer-shell residual increments on the same physical
Hartree orbit gain one locked positive order. Unlike a bare finite
atom bookkeeping theorem, every increment is the complete original
Hartree PDE residual, including all quartic nonlocal cross interactions
with the actual previous finite Kummer field. -/
theorem actual_Hartree_finite_physical_Kummer_full_PDE_order_bound
    (s : ℝ) (hs : 1 ≤ s)
    (packets : List (ActualKummerPhysicalShellPacket s))
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega r B A beta rhoStar N : ℝ)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hbeta : 1 / 2 < beta) (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (htrap : ell s ≤ s ^ (-beta))
    (hz : Measurable (z (time s)))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (haGlobal : ∀ P ∈ packets, ∀ t : ℝ, 0 < P.a t)
    (haCont : ∀ P ∈ packets, ContinuousAt P.a s)
    (hXlow : ∀ P ∈ packets,
      actualHartreeSlowInnerRadius (ell s) ≤ P.a s * P.R)
    (hSep : ∀ P ∈ packets, 2 * r ≤ P.a s * P.R)
    (hN : ∀ P ∈ packets,
      N ≤ P.rho + actualHartreeLockedKappa beta rhoStar) :
    ‖actualKummerFinitePhysicalPDEGap packets
        ell c time z b omega r‖ ≤
      actualKummerFinitePhysicalPDEConstant packets B A *
        s ^ (-N) := by
  induction packets with
  | nil =>
      have hZero :
          actualKummerFinitePhysicalPDEGap
            ([] : List (ActualKummerPhysicalShellPacket s))
            ell c time z b omega r = 0 := by
        unfold actualKummerFinitePhysicalPDEGap
        have hEq :
            (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
              actualKummerFinitePhysicalTail
                ([] : List (ActualKummerPhysicalShellPacket s)) t y) =
            actualKummerFinitePhysicalBase ell c time z := by
          funext t y
          simp [actualKummerFinitePhysicalTail]
        rw [hEq]
        ring
      rw [hZero]
      simp [actualKummerFinitePhysicalPDEConstant]
  | cons P ps ih =>
      have hTailGlobal : ∀ Q ∈ ps, ∀ t : ℝ, 0 < Q.a t := by
        intro Q hQ
        exact haGlobal Q (by simp [hQ])
      have hTailCont : ∀ Q ∈ ps, ContinuousAt Q.a s := by
        intro Q hQ
        exact haCont Q (by simp [hQ])
      have hTailXlow : ∀ Q ∈ ps,
          actualHartreeSlowInnerRadius (ell s) ≤ Q.a s * Q.R := by
        intro Q hQ
        exact hXlow Q (by simp [hQ])
      have hTailSep : ∀ Q ∈ ps, 2 * r ≤ Q.a s * Q.R := by
        intro Q hQ
        exact hSep Q (by simp [hQ])
      have hTailN : ∀ Q ∈ ps,
          N ≤ Q.rho + actualHartreeLockedKappa beta rhoStar := by
        intro Q hQ
        exact hN Q (by simp [hQ])
      have hTail := ih hTailGlobal hTailCont hTailXlow hTailSep hTailN
      have hKh : actualKummerRepairCenterTimeGain beta ≤ 1 / 2 := by
        unfold actualKummerRepairCenterTimeGain
        exact min_le_right _ _
      have hRho :
          (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤
            P.rho := by
        have hh := P.rho_half
        linarith
      have hStepRaw :=
        actual_Hartree_finite_prior_Kummer_repairs_next_PDE_locked_gain
          s hs ps P.a ell c time P.R P.p P.q z
          b omega r B A beta rhoStar P.rho P.CX P.CD
          (haGlobal P (by simp)) (haCont P (by simp))
          P.R_pos hell hellOne hc hB hA hbeta hrhoStar hflat
          hRho htrap (hXlow P (by simp))
          P.CX_nonneg P.radius_bound P.CD_nonneg P.jet_bound
          hz hSup hStrauss hr hrOne (hSep P (by simp))
      dsimp only at hStepRaw
      let CH := actualKummerFinitePhysicalTailConstant ps
      let Ct := actualKummerRepairCorrectedTimeConstant
        B A CH P.CX P.CD
      let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
      let C0 := 2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3
      have hStep :
          ‖complexRadialRenormalizedResidual
             (fun t y =>
                actualKummerFinitePhysicalBase ell c time z t y +
                actualKummerFinitePhysicalTail ps t y +
                actualKummerPhysicalPacketTail P t y) b omega s r -
            complexRadialRenormalizedResidual
             (fun t y =>
                actualKummerFinitePhysicalBase ell c time z t y +
                actualKummerFinitePhysicalTail ps t y) b omega s r‖ ≤
            C0 * s ^ (-(P.rho +
              actualHartreeLockedKappa beta rhoStar)) := by
        simpa only [actualKummerFinitePhysicalBase,
          actualKummerPhysicalPacketTail, C0, Ct, M, CH]
          using hStepRaw
      have hNstep :
          N ≤ P.rho + actualHartreeLockedKappa beta rhoStar :=
        hN P (by simp)
      have hPow :
          s ^ (-(P.rho + actualHartreeLockedKappa beta rhoStar)) ≤
            s ^ (-N) :=
        Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg hNstep)
      have hCH0 : 0 ≤ CH :=
        actual_Kummer_finite_physical_tail_constant_nonneg ps
      have hCt0 : 0 ≤ Ct := by
        have hm := monopoleRadialBoundConstant_pos.le
        dsimp [Ct, actualKummerRepairCorrectedTimeConstant]
        have hc0 := P.CX_nonneg
        have hd0 := P.CD_nonneg
        positivity
      have hM0 : 0 ≤ M := by
        have hm := monopoleRadialBoundConstant_pos.le
        dsimp [M]
        positivity
      have hC0 : 0 ≤ C0 := by
        dsimp [C0]
        unfold hartreeKappa
        positivity
      have hStepN : _ ≤ C0 * s ^ (-N) :=
        hStep.trans (mul_le_mul_of_nonneg_left hPow hC0)
      have hCons :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail (P :: ps) t y) =
          (fun t y =>
            actualKummerFinitePhysicalBase ell c time z t y +
              actualKummerFinitePhysicalTail ps t y +
                actualKummerPhysicalPacketTail P t y) := by
        funext t y
        change actualKummerFinitePhysicalBase ell c time z t y +
          (actualKummerPhysicalPacketTail P t y +
            actualKummerFinitePhysicalTail ps t y) =
          actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail ps t y +
              actualKummerPhysicalPacketTail P t y
        abel
      have hGap :
          actualKummerFinitePhysicalPDEGap (P :: ps)
              ell c time z b omega r =
            (complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualKummerFinitePhysicalTail ps t y +
                actualKummerPhysicalPacketTail P t y) b omega s r -
              complexRadialRenormalizedResidual
                (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                  actualKummerFinitePhysicalTail ps t y) b omega s r) +
            actualKummerFinitePhysicalPDEGap ps ell c time z b omega r := by
        unfold actualKummerFinitePhysicalPDEGap
        rw [hCons]
        ring
      rw [hGap]
      have hBound := norm_add_le
        (complexRadialRenormalizedResidual
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail ps t y +
            actualKummerPhysicalPacketTail P t y) b omega s r -
        complexRadialRenormalizedResidual
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFinitePhysicalTail ps t y) b omega s r)
        (actualKummerFinitePhysicalPDEGap ps ell c time z b omega r)
      calc
        _ ≤
          ‖complexRadialRenormalizedResidual
            (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
              actualKummerFinitePhysicalTail ps t y +
              actualKummerPhysicalPacketTail P t y) b omega s r -
            complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualKummerFinitePhysicalTail ps t y) b omega s r‖ +
          ‖actualKummerFinitePhysicalPDEGap ps ell c time z b omega r‖ :=
            hBound
        _ ≤ C0 * s ^ (-N) +
            actualKummerFinitePhysicalPDEConstant ps B A *
              s ^ (-N) :=
          add_le_add hStepN hTail
        _ = actualKummerFinitePhysicalPDEConstant (P :: ps) B A *
            s ^ (-N) := by
          change C0 * s ^ (-N) +
            actualKummerFinitePhysicalPDEConstant ps B A * s ^ (-N) =
            (C0 + actualKummerFinitePhysicalPDEConstant ps B A) *
              s ^ (-N)
          ring

end HBL.TypeIIDynamicSelection
