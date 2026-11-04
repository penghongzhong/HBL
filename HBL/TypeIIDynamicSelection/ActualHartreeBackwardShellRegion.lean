import HBL.TypeIIDynamicSelection.ActualHartreeMatchedShellWeightedGain
import Mathlib.Tactic

/-!
The backward shell uses R=L/2 and the SAME a>=L^3 region already used by
the complete compatibility matrix. Enlarging its fixed lower threshold
also supplies the weak Kummer absorption budget. The second scale term
in the actual weighted shell error is then no larger than its R^{-3/4}
term. No rate law or recursive residual estimate is assumed here.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The existing cubic separation of physical scales supplies the entire
weak Kummer budget after enlarging one fixed lower-radius threshold. -/
theorem actual_Hartree_backward_shell_weak_budget
    (mu theta L a : ℝ)
    (hL : max 6 (4 * (1 + ‖frozenZeroCoeff mu theta‖)) ≤ L)
    (ha : L ^ 3 ≤ a) :
    2 < L / 2 ∧
      16 * (L / 2) ^ 2 * ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1 := by
  have hLsix : 6 ≤ L := (le_max_left _ _).trans hL
  have hLk : 4 * (1 + ‖frozenZeroCoeff mu theta‖) ≤ L :=
    (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hapos : 0 < a := (pow_pos hLpos 3).trans_le ha
  have hLfour : L ≤ L ^ 4 := by
    have h := mul_le_mul_of_nonneg_left
      (show 1 ≤ L ^ 3 from one_le_pow₀ hLone) hLpos.le
    nlinarith only [h]
  have hLa : L ^ 6 ≤ a ^ 2 := by
    have h := pow_le_pow_left₀ (pow_nonneg hLpos.le 3) ha 2
    simpa only [← pow_mul] using h
  have hbound : 4 * (1 + ‖frozenZeroCoeff mu theta‖) * L ^ 2 ≤ a ^ 2 := by
    calc
      _ ≤ L ^ 4 * L ^ 2 :=
        mul_le_mul_of_nonneg_right (hLk.trans hLfour) (sq_nonneg L)
      _ = L ^ 6 := by ring
      _ ≤ a ^ 2 := hLa
  refine ⟨by linarith, ?_⟩
  calc
    _ = (4 * (1 + ‖frozenZeroCoeff mu theta‖) * L ^ 2) / a ^ 2 := by ring
    _ ≤ 1 := (div_le_iff₀ (pow_pos hapos 2)).2 (by simpa only [one_mul] using hbound)

/-- The full weighted shell factor has a genuine negative radius power
on the same physical separation region as the constructed matrix. -/
theorem actual_Hartree_backward_shell_relative_factor
    (L a C0 C1 : ℝ) (hL : 2 ≤ L) (ha : L ^ 3 ≤ a)
    (hC1 : 0 ≤ C1) :
    C0 * (L / 2) ^ (-(3 / 4 : ℝ)) +
        C1 * (L / 2) ^ (13 / 4 : ℝ) / a ^ 2 ≤
      (C0 + C1) * (L / 2) ^ (-(3 / 4 : ℝ)) := by
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hRpos : 0 < L / 2 := by positivity
  have hLthree : L ^ 2 ≤ L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hLone (sq_nonneg L)
    nlinarith only [h]
  have hRa : (L / 2) ^ 2 ≤ a := by
    calc
      _ ≤ L ^ 2 := pow_le_pow_left₀ hRpos.le (by linarith) 2
      _ ≤ L ^ 3 := hLthree
      _ ≤ a := ha
  have hDenom : (L / 2) ^ 4 ≤ a ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg (L / 2)) hRa 2
    simpa only [← pow_mul] using h
  have hpower : (L / 2) ^ (13 / 4 : ℝ) / (L / 2) ^ 4 =
      (L / 2) ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast (L / 2) 4, ← Real.rpow_sub hRpos]
    norm_num
  have hratio : (L / 2) ^ (13 / 4 : ℝ) / a ^ 2 ≤
      (L / 2) ^ (-(3 / 4 : ℝ)) := by
    calc
      _ ≤ (L / 2) ^ (13 / 4 : ℝ) / (L / 2) ^ 4 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hRpos.le _)
          (pow_pos hRpos 4) hDenom
      _ = _ := hpower
  calc
    _ = C0 * (L / 2) ^ (-(3 / 4 : ℝ)) +
        C1 * ((L / 2) ^ (13 / 4 : ℝ) / a ^ 2) := by ring
    _ ≤ C0 * (L / 2) ^ (-(3 / 4 : ℝ)) +
        C1 * (L / 2) ^ (-(3 / 4 : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hratio hC1)
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
