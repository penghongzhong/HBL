import HBL.TypeIIDynamicSelection.ActualKummerMovingTailTruePDEResidual
import HBL.TypeIIDynamicSelection.ActualKummerRepairClockSqrtRadius
import Mathlib.Tactic

/-!
# The actual Kummer replacement is in the next-layer bubble envelope class

The nonlinear Hartree iteration requires the current physical correction H
to admit a global estimate ||H(s,r)|| <= CH*bubble(r). This is NOT assumed
for the actual compact Kummer replacement. We derive it directly from its
true moving shell support, its source-selected upper boundary jet
||p(s)||+R||q(s)|| <= CD*s^(-rho), and the exact sqrt-clock shell bound
a(s)R <= CX*s^(1/2).

For rho >= 1/2, one constant (1+2CX)*CD works for ALL positive radii,
without a prescribed Type-II rate. This supplies an honest producer of
the next corrected-background Hartree PDE input.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual moving Kummer repair tail itself satisfies the global
physical bubble envelope under only its selected upper-jet and clock
bounds. There is no artificial globally supported affine repair. -/
theorem actual_Kummer_physical_outer_repair_bubble_from_clock
    (a : ℝ → ℝ) (R : ℝ) (p q : ℝ → ℂ)
    (s rho CX CD : ℝ)
    (ha : 0 < a s) (hR : 0 < R)
    (hs : 1 ≤ s) (hrho : (1 / 2 : ℝ) ≤ rho)
    (hCX : 0 ≤ CX) (hCD : 0 ≤ CD)
    (hX : a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hJet : ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho)) :
    ∀ y : ℝ, 0 < y →
      ‖actualKummerPhysicalOuterRepair a R p q s y‖ ≤
        ((1 + 2 * CX) * CD) * bubble y := by
  obtain ⟨C1,C2,_hC1,_hC2,hRepair⟩ :=
    actual_Kummer_interface_repair_positive_radius_bound
  let X : ℝ := a s * R
  let D : ℝ := ‖p s‖ + R * ‖q s‖
  let CH : ℝ := (1 + 2 * CX) * CD
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCH : 0 ≤ CH := by dsimp [CH]; positivity
  have hs0 : 0 ≤ s := by linarith
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hPowRhoOne : s ^ (-rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have hDone : D ≤ CD := by
    calc
      D ≤ CD * s ^ (-rho) := by simpa only [D] using hJet
      _ ≤ CD * 1 :=
        mul_le_mul_of_nonneg_left hPowRhoOne hCD
      _ = CD := by ring
  have hX0 : 0 ≤ X := (mul_pos ha hR).le
  have hDco : 0 ≤ CD * s ^ (-rho) :=
    mul_nonneg hCD (Real.rpow_nonneg hs0 _)
  have hXco : 0 ≤ CX * s ^ (1 / 2 : ℝ) :=
    mul_nonneg hCX (Real.rpow_nonneg hs0 _)
  have hProd :
      X * D ≤ (CX * s ^ (1 / 2 : ℝ)) * (CD * s ^ (-rho)) :=
    mul_le_mul hX (by simpa only [D] using hJet) hD hXco
  have hPow :
      s ^ (1 / 2 : ℝ) * s ^ (-rho) =
        s ^ (1 / 2 - rho) := by
    rw [← Real.rpow_add hspos]
    congr 1
  have hExp : s ^ (1 / 2 - rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have hXDone : X * D ≤ CX * CD := by
    calc
      _ ≤ (CX * s ^ (1 / 2 : ℝ)) * (CD * s ^ (-rho)) := hProd
      _ = (CX * CD) * (s ^ (1 / 2 : ℝ) * s ^ (-rho)) := by ring
      _ = (CX * CD) * s ^ (1 / 2 - rho) := by rw [hPow]
      _ ≤ (CX * CD) * 1 :=
        mul_le_mul_of_nonneg_left hExp (mul_nonneg hCX hCD)
      _ = CX * CD := by ring
  intro y hy
  by_cases hyShell : y ∈ Ioc X (2 * X)
  · have hyPhys : y / a s ∈ Icc R (2 * R) := by
      constructor
      · apply (le_div_iff₀ ha).2
        simpa only [X,mul_comm] using hyShell.1.le
      · apply (div_le_iff₀ ha).2
        simpa only [X,mul_assoc,mul_comm,mul_left_comm] using hyShell.2
    have hVal :
        ‖actualKummerPhysicalOuterRepair a R p q s y‖ ≤ D := by
      unfold actualKummerPhysicalOuterRepair
      rw [Set.indicator_of_mem (by simpa only [X, mul_assoc] using hyShell)]
      change ‖actualKummerInterfaceRepair R (p s) (q s) (y / a s)‖ ≤ D
      exact (hRepair 0 0 R (y / a s) hR hyPhys (p s) (q s)).1
    have hGeom : Real.sqrt (1 + y ^ 2) ≤ 1 + y := by
      calc
        _ ≤ Real.sqrt ((1 + y) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hy.le])
        _ = 1 + y := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith)]
    have hSqrtPos : 0 < Real.sqrt (1 + y ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    have hInv : (1 + y)⁻¹ ≤ bubble y := by
      have hi := inv_anti₀ hSqrtPos hGeom
      change (1 + y)⁻¹ ≤ bubble y at hi
      exact hi
    have hYprod : y * D ≤ (2 * X) * D :=
      mul_le_mul_of_nonneg_right hyShell.2 hD
    have hYD : (1 + y) * D ≤ CH := by
      calc
        (1 + y) * D = D + y * D := by ring
        _ ≤ D + (2 * X) * D := add_le_add (le_refl D) hYprod
        _ = D + 2 * (X * D) := by ring
        _ ≤ CD + 2 * (CX * CD) :=
          add_le_add hDone (mul_le_mul_of_nonneg_left hXDone (by norm_num))
        _ = CH := by dsimp [CH]; ring
    have hDb : D ≤ CH / (1 + y) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + y)).2
      simpa only [mul_comm] using hYD
    calc
      ‖actualKummerPhysicalOuterRepair a R p q s y‖ ≤ D := hVal
      _ ≤ CH / (1 + y) := hDb
      _ = CH * (1 + y)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ CH * bubble y := mul_le_mul_of_nonneg_left hInv hCH
  · have hQ :
        actualKummerPhysicalOuterRepair a R p q s y = 0 := by
      have hnot : y ∉ Ioc (a s * R) (2 * a s * R) := by
        simpa only [X, mul_assoc] using hyShell
      unfold actualKummerPhysicalOuterRepair
      rw [Set.indicator_of_notMem hnot]
    rw [hQ, norm_zero]
    exact mul_nonneg hCH (bubble_nonneg y)

end HBL.TypeIIDynamicSelection
