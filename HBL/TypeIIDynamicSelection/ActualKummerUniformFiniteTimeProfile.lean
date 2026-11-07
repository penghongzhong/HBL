import HBL.TypeIIDynamicSelection.ActualKummerPhysicalTailWeightedLipschitz
import HBL.TypeIIDynamicSelection.ActualKummerFinitePhysicalRepairsNextGain
import Mathlib.Tactic

/-!
# Uniform-time finite realization of actual moving Kummer corrections

The earlier single-time packet is insufficient for a whole-interval
parametrix: its constants may depend on the chosen time. Here every
packet carries a SINGLE physical moving scale, genuine boundary-jet
paths and real constants CX, CD that are valid on the entire
renormalized terminal half-line [s0,+infty).

The literal finite sum of actual compact Kummer replacement fields
therefore has a time-UNIFORM bound with an explicitly constructed
time-independent constant and a genuine positive bubble time gain:
  ||sum_j H_j(s,r)|| <= C s^(-delta) bubble(r).
No per-time choice of constants, arbitrary generated-term order tag,
prescribed Type-II blowup rate or artificial free homogeneous tail appears.

This proves only the finite Kummer correction envelope; complete
three-region C1 and weighted PDE source gluing remain separate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- One original physical Kummer moving repair and *uniform* source
estimate along a single true modulation trajectory. -/
structure ActualKummerUniformPhysicalTailPacket (s0 delta : ℝ) where
  a : ℝ → ℝ
  R : ℝ
  p q : ℝ → ℂ
  rho CX CD : ℝ
  Rpos : 0 < R
  aPos : ∀ s : ℝ, s0 ≤ s → 0 < a s
  rhoGain : 1 / 2 + delta ≤ rho
  CX_nonneg : 0 ≤ CX
  CD_nonneg : 0 ≤ CD
  radius : ∀ s : ℝ, s0 ≤ s →
    a s * R ≤ CX * s ^ (1 / 2 : ℝ)
  jet : ∀ s : ℝ, s0 ≤ s →
    ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho)

/-- The literal finite Hartree Kummer repair field on the entire time
half-line, with no fixed-time packet or recomputed bound constant. -/
def actualKummerUniformPhysicalTail
    {s0 delta : ℝ}
    (packets : List (ActualKummerUniformPhysicalTailPacket s0 delta))
    (s y : ℝ) : ℂ :=
  (packets.map (fun P =>
    actualKummerPhysicalOuterRepair P.a P.R P.p P.q s y)).sum

def actualKummerUniformPhysicalTailConstant
    {s0 delta : ℝ}
    (packets : List (ActualKummerUniformPhysicalTailPacket s0 delta)) : ℝ :=
  (packets.map (fun P => (1 + 2 * P.CX) * P.CD)).sum

theorem actual_Kummer_uniform_physical_tail_constant_nonneg
    {s0 delta : ℝ}
    (packets : List (ActualKummerUniformPhysicalTailPacket s0 delta)) :
    0 ≤ actualKummerUniformPhysicalTailConstant packets := by
  induction packets with
  | nil =>
      simp [actualKummerUniformPhysicalTailConstant]
  | cons P ps ih =>
      have hP : 0 ≤ (1 + 2 * P.CX) * P.CD := by
        have hc := P.CX_nonneg
        have hd := P.CD_nonneg
        positivity
      change 0 ≤
        (1 + 2 * P.CX) * P.CD +
          actualKummerUniformPhysicalTailConstant ps
      exact add_nonneg hP ih

/-- Strict positive uniform bubble order for the actual finite
moving Kummer correction along ONE time-dependent physical orbit. -/
theorem actual_Kummer_uniform_finite_repair_positive_time_gain
    {s0 delta : ℝ}
    (packets : List (ActualKummerUniformPhysicalTailPacket s0 delta))
    (hs0 : 1 ≤ s0) (hdelta : 0 < delta) :
    ∀ s : ℝ, s0 ≤ s → ∀ y : ℝ, 0 < y →
      ‖actualKummerUniformPhysicalTail packets s y‖ ≤
        actualKummerUniformPhysicalTailConstant packets *
          s ^ (-delta) * bubble y := by
  intro s hs y hy
  have hs1 : 1 ≤ s := hs0.trans hs
  induction packets with
  | nil =>
      simp [actualKummerUniformPhysicalTail,
        actualKummerUniformPhysicalTailConstant]
  | cons P ps ih =>
      have hRhoExp :
          s ^ (-(P.rho - 1 / 2 : ℝ)) ≤ s ^ (-delta) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (by linarith [P.rhoGain])
      have hRaw :=
        actual_Kummer_physical_outer_repair_bubble_time_gain
          P.a P.R P.p P.q s P.rho P.CX P.CD
          (P.aPos s hs) P.Rpos hs1 P.CX_nonneg P.CD_nonneg
          (P.radius s hs) (P.jet s hs) y hy
      have hC : 0 ≤ (1 + 2 * P.CX) * P.CD := by
        have hc := P.CX_nonneg
        have hd := P.CD_nonneg
        positivity
      have hBubble : 0 ≤ bubble y := bubble_nonneg y
      have hP :
          ‖actualKummerPhysicalOuterRepair P.a P.R P.p P.q s y‖ ≤
            ((1 + 2 * P.CX) * P.CD) *
              s ^ (-delta) * bubble y := by
        calc
          _ ≤ ((1 + 2 * P.CX) * P.CD) *
                s ^ (-(P.rho - 1 / 2 : ℝ)) * bubble y := hRaw
          _ ≤ ((1 + 2 * P.CX) * P.CD) *
                s ^ (-delta) * bubble y :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hRhoExp hC) hBubble
      change
        ‖actualKummerPhysicalOuterRepair P.a P.R P.p P.q s y +
          actualKummerUniformPhysicalTail ps s y‖ ≤
        ((1 + 2 * P.CX) * P.CD +
          actualKummerUniformPhysicalTailConstant ps) *
          s ^ (-delta) * bubble y
      calc
        _ ≤ ‖actualKummerPhysicalOuterRepair P.a P.R P.p P.q s y‖ +
            ‖actualKummerUniformPhysicalTail ps s y‖ :=
          norm_add_le _ _
        _ ≤ ((1 + 2 * P.CX) * P.CD) *
              s ^ (-delta) * bubble y +
            actualKummerUniformPhysicalTailConstant ps *
              s ^ (-delta) * bubble y :=
          add_le_add hP ih
        _ = ((1 + 2 * P.CX) * P.CD +
            actualKummerUniformPhysicalTailConstant ps) *
            s ^ (-delta) * bubble y := by ring

end HBL.TypeIIDynamicSelection
