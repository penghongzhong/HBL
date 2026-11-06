import HBL.TypeIIDynamicSelection.ActualKummerPhysicalRepairTimeDerivative
import Mathlib.Tactic

/-!
# The physical Kummer repair time derivative is a next-layer source

This is a thin quantitative consumer of the exact repair time derivative.
It makes the remaining producer interface explicit: current jet size,
relative physical-scale speed, and upper-jet speed.

No decay for those three inputs is invented here.  Once supplied by the
selected source/clock construction, the actual time derivative has the
same rho+kappa next-layer order.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_Kummer_physical_interface_repair_time_next_layer :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∀ (a : ℝ → ℝ) (p q : ℝ → ℂ)
      (R y s adot rho kappa CD CA CJ : ℝ) (pdot qdot : ℂ),
      HasDerivAt a adot s → 0 < a s →
      HasDerivAt p pdot s → HasDerivAt q qdot s →
      0 < R → y ∈ Icc (a s * R) (2 * a s * R) →
      1 ≤ s → 0 ≤ CD → 0 ≤ CA → 0 ≤ CJ →
      (‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho)) →
      (|adot| / a s ≤ CA * s ^ (-kappa)) →
      (‖pdot‖ + R * ‖qdot‖ ≤
        CJ * s ^ (-(rho + kappa))) →
      ‖deriv
          (fun t => actualKummerPhysicalInterfaceRepair
            (a t) R (p t) (q t) y) s‖ ≤
        (2 * (3 * C1 + 1) * CD * CA + CJ) *
          s ^ (-(rho + kappa)) := by
  obtain ⟨C1,C2,hC1,hC2,hShell⟩ :=
    actual_Kummer_physical_interface_repair_time_shell_bound
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro a p q R y s adot rho kappa CD CA CJ pdot qdot
    ha haPos hp hq hR hy hs hCD hCA hCJ hD hRel hJet
  have hRaw := hShell a p q R y s adot pdot qdot
    ha haPos hp hq hR hy
  dsimp only at hRaw
  let K1 : ℝ := 2 * (3 * C1 + 1)
  have hK1 : 0 ≤ K1 := by
    dsimp [K1]
    positivity
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hPowRho : 0 ≤ s ^ (-rho) := Real.rpow_nonneg hs0 _
  have hPowK : 0 ≤ s ^ (-kappa) := Real.rpow_nonneg hs0 _
  have hKD :
      K1 * (‖p s‖ + R * ‖q s‖) ≤
        K1 * (CD * s ^ (-rho)) :=
    mul_le_mul_of_nonneg_left hD hK1
  have hTerm0 :
      (K1 * (‖p s‖ + R * ‖q s‖)) * (|adot| / a s) ≤
        (K1 * (CD * s ^ (-rho))) * (CA * s ^ (-kappa)) := by
    exact mul_le_mul hKD hRel
      (div_nonneg (abs_nonneg adot) haPos.le)
      (mul_nonneg hK1 (mul_nonneg hCD hPowRho))
  have hPow :
      s ^ (-rho) * s ^ (-kappa) =
        s ^ (-(rho + kappa)) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  have hTerm :
      (2 * (3 * C1 + 1) * (‖p s‖ + R * ‖q s‖)) *
          (|adot| / a s) ≤
        (2 * (3 * C1 + 1) * CD * CA) *
          s ^ (-(rho + kappa)) := by
    change
      (K1 * (‖p s‖ + R * ‖q s‖)) * (|adot| / a s) ≤ _
    calc
      _ ≤ (K1 * (CD * s ^ (-rho))) *
          (CA * s ^ (-kappa)) := hTerm0
      _ = (2 * (3 * C1 + 1) * CD * CA) *
          (s ^ (-rho) * s ^ (-kappa)) := by
        dsimp [K1]
        ring
      _ = _ := by rw [hPow]
  calc
    _ ≤ (2 * (3 * C1 + 1) * (‖p s‖ + R * ‖q s‖)) *
          (|adot| / a s) + (‖pdot‖ + R * ‖qdot‖) := by
      simpa only [add_assoc] using hRaw
    _ ≤ (2 * (3 * C1 + 1) * CD * CA) *
          s ^ (-(rho + kappa)) +
        CJ * s ^ (-(rho + kappa)) :=
      add_le_add hTerm hJet
    _ = (2 * (3 * C1 + 1) * CD * CA + CJ) *
          s ^ (-(rho + kappa)) := by ring

end HBL.TypeIIDynamicSelection
