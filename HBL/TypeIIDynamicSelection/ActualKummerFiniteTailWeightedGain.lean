import HBL.TypeIIDynamicSelection.ActualKummerFinitePhysicalRepairsNextGain
import HBL.TypeIIDynamicSelection.ActualKummerPhysicalTailWeightedLipschitz
import Mathlib.Tactic

/-!
# Strict time-decaying physical bubble bound for finite ACTUAL Kummer corrections

The literal finite sum of already selected physical Kummer tails is not
just pointwise controlled by a fixed bubble envelope. If all their
true upper boundary-jet orders are at least 1/2+delta, then the FULL
finite correction itself is O(s^(-delta) bubble(r)), with a constant
equal to the actual sum of selected physical shell coefficients.

This is a genuine quantitative next-layer class for physical Hartree
finite-profile recursion. It is not a substitute for C1 gluing at the
left Kummer interface or the full three-region parametrix construction.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Kummer_finite_physical_tail_positive_time_bubble_gain
    (s delta : ℝ) (hs : 1 ≤ s) (_hdelta : 0 < delta)
    (packets : List (ActualKummerPhysicalShellPacket s))
    (hOrders : ∀ P ∈ packets, 1 / 2 + delta ≤ P.rho)
    (y : ℝ) (hy : 0 < y) :
    ‖actualKummerFinitePhysicalTail packets s y‖ ≤
      actualKummerFinitePhysicalTailConstant packets *
        s ^ (-delta) * bubble y := by
  induction packets with
  | nil =>
      simp [actualKummerFinitePhysicalTail,
        actualKummerFinitePhysicalTailConstant]
  | cons P ps ih =>
      have hOrder : 1 / 2 + delta ≤ P.rho :=
        hOrders P (by simp)
      have hTailOrders :
          ∀ Q ∈ ps, 1 / 2 + delta ≤ Q.rho := by
        intro Q hQ
        exact hOrders Q (by simp [hQ])
      have hTail := ih hTailOrders
      have hRaw :=
        actual_Kummer_physical_outer_repair_bubble_time_gain
          P.a P.R P.p P.q s P.rho P.CX P.CD
          P.a_pos P.R_pos hs P.CX_nonneg P.CD_nonneg
          P.radius_bound P.jet_bound y hy
      have hExponents :
          s ^ (-(P.rho - 1 / 2 : ℝ)) ≤ s ^ (-delta) :=
        Real.rpow_le_rpow_of_exponent_le hs (by linarith)
      have hC : 0 ≤ (1 + 2 * P.CX) * P.CD := by
        have hc := P.CX_nonneg
        have hd := P.CD_nonneg
        positivity
      have hBubble : 0 ≤ bubble y := bubble_nonneg y
      have hCurrent :
          ‖actualKummerPhysicalPacketTail P s y‖ ≤
            ((1 + 2 * P.CX) * P.CD) * s ^ (-delta) * bubble y := by
        calc
          _ ≤ ((1 + 2 * P.CX) * P.CD) *
              s ^ (-(P.rho - 1 / 2 : ℝ)) * bubble y := by
            simpa only [actualKummerPhysicalPacketTail] using hRaw
          _ ≤ ((1 + 2 * P.CX) * P.CD) *
              s ^ (-delta) * bubble y :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hExponents hC) hBubble
      change
        ‖actualKummerPhysicalPacketTail P s y +
          actualKummerFinitePhysicalTail ps s y‖ ≤
        ((1 + 2 * P.CX) * P.CD +
          actualKummerFinitePhysicalTailConstant ps) *
            s ^ (-delta) * bubble y
      calc
        _ ≤ ‖actualKummerPhysicalPacketTail P s y‖ +
            ‖actualKummerFinitePhysicalTail ps s y‖ :=
          norm_add_le _ _
        _ ≤ ((1 + 2 * P.CX) * P.CD) *
              s ^ (-delta) * bubble y +
            actualKummerFinitePhysicalTailConstant ps *
              s ^ (-delta) * bubble y :=
          add_le_add hCurrent hTail
        _ = ((1 + 2 * P.CX) * P.CD +
            actualKummerFinitePhysicalTailConstant ps) *
              s ^ (-delta) * bubble y := by ring

end HBL.TypeIIDynamicSelection
