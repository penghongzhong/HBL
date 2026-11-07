import HBL.TypeIIDynamicSelection.ActualKummerRepairPhysicalH1ShellEnergy
import HBL.TypeIIDynamicSelection.ActualKummerRepairCenterTimeGain
import Mathlib.Tactic

/-!
# Positive three-dimensional Hdot1 energy gain for the physical Kummer tail

The actual repair's radial-gradient shell integral is O(X D²),
where X=aR is the genuine physical shell and D is the full value/slope jet.
The exact slice clock gives X=O(s^(1/2)); hence whenever
    2*rho >= 1/2 + kappa_center,
the physical energy integral itself gains s^(-kappa_center).

The full quartic Hartree center estimate has the SAME lowered threshold.
This is the energy-side counterpart needed for revised §2.13. It does not
assume or assert that every other profile piece is small.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_Kummer_physical_repair_shell_H1_positive_time_gain :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ (a R s beta rho CX CD : ℝ),
        0 < a → 0 < R → 1 ≤ s →
        1 / 2 < beta →
        (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho →
        0 ≤ CX → 0 ≤ CD →
        a * R ≤ CX * s ^ (1 / 2 : ℝ) →
      ∀ (p q : ℂ),
        ‖p‖ + R * ‖q‖ ≤ CD * s ^ (-rho) →
        let k := actualKummerRepairCenterTimeGain beta
        0 < k ∧
        (∫ y in Icc (a * R) (2 * a * R),
          y ^ 2 *
            ‖deriv (actualKummerPhysicalInterfaceRepair a R p q) y‖ ^ 2) ≤
          (4 * (3 * C1 + 1) ^ 2 * CX * CD ^ 2) *
            s ^ (-k) := by
  obtain ⟨C1,C2,hC1,hC2,hEnergy⟩ :=
    actual_Kummer_physical_interface_repair_radial_shell_H1_energy
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro a R s beta rho CX CD ha hR hs hbeta hrho hCX hCD hX p q hJet
  dsimp only
  let k := actualKummerRepairCenterTimeGain beta
  let D : ℝ := ‖p‖ + R * ‖q‖
  let K : ℝ := 4 * (3 * C1 + 1) ^ 2
  have hkpos : 0 < k :=
    actual_Kummer_repair_center_time_gain_positive beta hbeta
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hD2 : D ^ 2 ≤ CD ^ 2 * s ^ (-2 * rho) := by
    have hRaw := pow_le_pow_left₀ hD (by simpa only [D] using hJet) 2
    calc
      D ^ 2 ≤ (CD * s ^ (-rho)) ^ 2 := hRaw
      _ = CD ^ 2 * (s ^ (-rho)) ^ 2 := by ring_nf
      _ = CD ^ 2 * s ^ (-2 * rho) := by
        rw [← Real.rpow_mul_natCast hs0 (-rho) 2]
        congr 1
        ring_nf
  have hX0 : 0 ≤ a * R := (mul_pos ha hR).le
  have hXco : 0 ≤ CX * s ^ (1 / 2 : ℝ) :=
    mul_nonneg hCX (Real.rpow_nonneg hs0 _)
  have hD2co : 0 ≤ CD ^ 2 * s ^ (-2 * rho) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  have hProduct :
      (a * R) * D ^ 2 ≤
        (CX * s ^ (1 / 2 : ℝ)) * (CD ^ 2 * s ^ (-2 * rho)) :=
    mul_le_mul hX hD2 (sq_nonneg _) hXco
  have hPow :
      s ^ (1 / 2 : ℝ) * s ^ (-2 * rho) =
        s ^ (1 / 2 - 2 * rho) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring_nf
  have hExp :
      s ^ (1 / 2 - 2 * rho) ≤ s ^ (-k) :=
    Real.rpow_le_rpow_of_exponent_le hs
      (by
        dsimp [k] at hrho ⊢
        linarith)
  have hProductTime :
      (a * R) * D ^ 2 ≤ (CX * CD ^ 2) * s ^ (-k) := by
    calc
      _ ≤ (CX * s ^ (1 / 2 : ℝ)) * (CD ^ 2 * s ^ (-2 * rho)) :=
        hProduct
      _ = (CX * CD ^ 2) * (s ^ (1 / 2 : ℝ) * s ^ (-2 * rho)) := by
        ring_nf
      _ = (CX * CD ^ 2) * s ^ (1 / 2 - 2 * rho) := by
        rw [hPow]
      _ ≤ (CX * CD ^ 2) * s ^ (-k) :=
        mul_le_mul_of_nonneg_left hExp
          (mul_nonneg hCX (sq_nonneg CD))
  have hRaw := hEnergy a R ha hR p q
  dsimp only at hRaw
  refine ⟨hkpos, ?_⟩
  calc
    _ ≤ K * ((a * R) * D ^ 2) := by
      simpa only [K, D, mul_assoc] using hRaw
    _ ≤ K * ((CX * CD ^ 2) * s ^ (-k)) :=
      mul_le_mul_of_nonneg_left hProductTime hK
    _ = (4 * (3 * C1 + 1) ^ 2 * CX * CD ^ 2) * s ^ (-k) := by
      dsimp [K]
      ring_nf

end HBL.TypeIIDynamicSelection
