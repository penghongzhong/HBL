import HBL.TypeIIDynamicSelection.ActualKummerRepairClockRadius
import Mathlib.Tactic

/-!
# Sharp square-root coarse Kummer radius from the physical slice clock

The already established trapped renormalized clock obeys q(s) <= 2 A s.
The exact physical identity a(s)^2 = q(s), a(s) >= 0, therefore yields
a(s) B <= sqrt(2 A) s^(1/2) at any normalized radius B <= 1.
This is stronger than the previously used O(s) fallback and does not
prescribe the Type-II concentrating scale or limiting modulation exponent.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

theorem actual_Kummer_repair_radius_sqrt_from_clock
    (a B q s Cq : ℝ)
    (ha : 0 ≤ a) (hB : B ≤ 1) (hs : 1 ≤ s)
    (hCq : 0 ≤ Cq) (haq : a ^ 2 = q) (hq : q ≤ Cq * s) :
    a * B ≤ Real.sqrt Cq * s ^ (1 / 2 : ℝ) := by
  have hAB : a * B ≤ a := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hB)]
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hq2 : a ^ 2 ≤ Cq * s := by
    rw [haq]
    exact hq
  have hSq : (Real.sqrt (Cq * s)) ^ 2 = Cq * s :=
    Real.sq_sqrt (mul_nonneg hCq hs0)
  have hRootNonneg : 0 ≤ Real.sqrt (Cq * s) :=
    Real.sqrt_nonneg _
  have hRoot : a ≤ Real.sqrt (Cq * s) := by
    nlinarith only [ha, hq2, hSq, hRootNonneg]
  calc
    a * B ≤ a := hAB
    _ ≤ Real.sqrt (Cq * s) := hRoot
    _ = Real.sqrt Cq * Real.sqrt s := Real.sqrt_mul hCq s
    _ = Real.sqrt Cq * s ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]

theorem actual_Kummer_repair_radius_sqrt_from_slice_clock
    {A s0 kappa delta H s a B : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs0 : 0 < s0)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s0 ≤ t → |h t| ≤ H * t ^ (-delta))
    (hsmall : (4 * H / (1 - delta)) * s0 ^ (-delta) ≤ A / 4)
    (hkappa : |kappa| ≤ A * s0 / 4)
    (hs : s0 ≤ s) (hs1 : 1 ≤ s)
    (ha : 0 ≤ a) (hB : B ≤ 1)
    (haq : a ^ 2 = HBL.Kinematic.sliceClock A s0 kappa h s) :
    a * B ≤ Real.sqrt (2 * A) * s ^ (1 / 2 : ℝ) := by
  have hq :=
    (HBL.Kinematic.sliceClock_linear_bounds h hA hs0 hdelta hdelta1
      hH hbound hsmall hkappa hs).2
  exact actual_Kummer_repair_radius_sqrt_from_clock
    a B (HBL.Kinematic.sliceClock A s0 kappa h s) s (2 * A)
    ha hB hs1 (by positivity) haq hq

end HBL.TypeIIDynamicSelection
