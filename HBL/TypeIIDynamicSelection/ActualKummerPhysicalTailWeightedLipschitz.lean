import HBL.TypeIIDynamicSelection.ActualKummerRepairBubbleEnvelopeFromClock
import Mathlib.Tactic

/-!
# Direct parameter-difference control for the ACTUAL moving Kummer repair

The original physical interface repair is exactly real/complex-linear in
its true upper boundary value and slope, with no free homogeneous mode.
The same statement holds for its genuinely supported moving outer tail
when the physical scale is fixed.

The exact sqrt-clock X=aR=O(s^(1/2)) loses precisely one half of the
source-jet time order in the global bubble envelope:
  ||Q(s,r)|| <= C s^(-(rho-1/2)) bubble(r).
The two-point version inherits this estimate from the ACTUAL selected
boundary-jet difference. No Frechet parameter derivative is required.

Physical parameter variation in a(s), R, the source, and the full quartic
Hartree residual remain separate genuine PDE tasks.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact complex-linear difference identity of the real smooth physical
Kummer repair; its left value/slope remain the true actual input jets. -/
theorem actual_Kummer_physical_interface_repair_jet_sub
    (a R y : ℝ) (p1 q1 p2 q2 : ℂ) :
    actualKummerPhysicalInterfaceRepair a R p1 q1 y -
      actualKummerPhysicalInterfaceRepair a R p2 q2 y =
    actualKummerPhysicalInterfaceRepair a R (p1 - p2) (q1 - q2) y := by
  unfold actualKummerPhysicalInterfaceRepair actualKummerInterfaceRepair
  ring

/-- The same exact jet subtraction for the ACTUAL moving compact outer
field. No globally supported affine substitute is used. -/
theorem actual_Kummer_physical_outer_repair_jet_sub
    (a : ℝ → ℝ) (R : ℝ) (p1 q1 p2 q2 : ℝ → ℂ)
    (s y : ℝ) :
    actualKummerPhysicalOuterRepair a R p1 q1 s y -
      actualKummerPhysicalOuterRepair a R p2 q2 s y =
    actualKummerPhysicalOuterRepair a R
      (fun t => p1 t - p2 t) (fun t => q1 t - q2 t) s y := by
  by_cases hy : y ∈ Ioc (a s * R) (2 * a s * R)
  · unfold actualKummerPhysicalOuterRepair
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
      Set.indicator_of_mem hy]
    exact actual_Kummer_physical_interface_repair_jet_sub
      (a s) R y (p1 s) (q1 s) (p2 s) (q2 s)
  · simp only [actualKummerPhysicalOuterRepair,
      Set.indicator_of_notMem hy, sub_self]

/-- A true upper-jet source of order rho yields a pointwise physical
bubble correction of order rho-1/2, rather than only a time-uniform
envelope. The loss is exactly the maximum physical sqrt-clock radius. -/
theorem actual_Kummer_physical_outer_repair_bubble_time_gain
    (a : ℝ → ℝ) (R : ℝ) (p q : ℝ → ℂ)
    (s rho CX CD : ℝ)
    (ha : 0 < a s) (hR : 0 < R)
    (hs : 1 ≤ s)
    (hCX : 0 ≤ CX) (hCD : 0 ≤ CD)
    (hX : a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hJet : ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho)) :
    ∀ y : ℝ, 0 < y →
      ‖actualKummerPhysicalOuterRepair a R p q s y‖ ≤
      ((1 + 2 * CX) * CD) *
        s ^ (-(rho - 1 / 2 : ℝ)) * bubble y := by
  let CD' : ℝ := CD * s ^ (-(rho - 1 / 2 : ℝ))
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hCD' : 0 ≤ CD' :=
    mul_nonneg hCD (Real.rpow_nonneg hspos.le _)
  have hExponents :
      s ^ (-(rho - 1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) =
        s ^ (-rho) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  have hJet' :
      ‖p s‖ + R * ‖q s‖ ≤ CD' * s ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ CD * s ^ (-rho) := hJet
      _ = CD' * s ^ (-(1 / 2 : ℝ)) := by
        dsimp [CD']
        rw [mul_assoc, hExponents]
  have hBound :=
    actual_Kummer_physical_outer_repair_bubble_from_clock
      a R p q s (1 / 2 : ℝ) CX CD'
      ha hR hs (by norm_num) hCX hCD' hX hJet'
  intro y hy
  simpa only [CD', mul_assoc] using hBound y hy

/-- Direct finite-parameter Lipschitz estimate of the ACTUAL Kummer
outer repair. The derivative-free estimate records the geometric 1/2
loss of the physical sqrt-clock shell rather than hiding it. -/
theorem actual_Kummer_outer_repair_direct_parameter_lipschitz
    (a : ℝ → ℝ) (R : ℝ)
    (p1 q1 p2 q2 : ℝ → ℂ)
    (s rho CX L : ℝ) (theta eta : ℝ × ℝ)
    (ha : 0 < a s) (hR : 0 < R) (hs : 1 ≤ s)
    (hCX : 0 ≤ CX) (hL : 0 ≤ L)
    (hX : a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hJetDifference :
      ‖p1 s - p2 s‖ + R * ‖q1 s - q2 s‖ ≤
        L * s ^ (-rho) * ‖theta - eta‖) :
    ∀ y : ℝ, 0 < y →
      ‖actualKummerPhysicalOuterRepair a R p1 q1 s y -
          actualKummerPhysicalOuterRepair a R p2 q2 s y‖ ≤
        ((1 + 2 * CX) * L) *
          s ^ (-(rho - 1 / 2 : ℝ)) * ‖theta - eta‖ * bubble y := by
  let CD : ℝ := L * ‖theta - eta‖
  have hCD : 0 ≤ CD := mul_nonneg hL (norm_nonneg _)
  have hJet :
      ‖p1 s - p2 s‖ + R * ‖q1 s - q2 s‖ ≤
        CD * s ^ (-rho) := by
    calc
      _ ≤ L * s ^ (-rho) * ‖theta - eta‖ := hJetDifference
      _ = CD * s ^ (-rho) := by dsimp [CD]; ring
  have hBound :=
    actual_Kummer_physical_outer_repair_bubble_time_gain
      a R (fun t => p1 t - p2 t) (fun t => q1 t - q2 t)
      s rho CX CD ha hR hs hCX hCD hX hJet
  intro y hy
  rw [actual_Kummer_physical_outer_repair_jet_sub]
  have h := hBound y hy
  calc
    _ ≤ ((1 + 2 * CX) * CD) *
      s ^ (-(rho - 1 / 2 : ℝ)) * bubble y := h
    _ = ((1 + 2 * CX) * L) *
      s ^ (-(rho - 1 / 2 : ℝ)) * ‖theta - eta‖ * bubble y := by
        dsimp [CD]
        ring

end HBL.TypeIIDynamicSelection
