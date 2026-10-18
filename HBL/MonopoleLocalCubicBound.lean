import HBL.MonopoleRadialBound
import HBL.MonopoleCutoffEquation
import HBL.MonopoleProfileCancellation

/-! A uniform quadratic bound for the actual truncated profile's local cubic term. -/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail

/-- The actual inner monopole in the radial coordinate, used at positive radii. -/
def monopoleInnerRadialProfile (R r : ℝ) : ℝ :=
  monopoleInnerProfile R r / r

/-- Truncation preserves the bound on the actual radial monopole, uniformly in the radius. -/
theorem monopoleInnerRadialProfile_abs_le {R r : ℝ} (hr : 0 < r) :
    |monopoleInnerRadialProfile R r| ≤ monopoleRadialBoundConstant := by
  have hcut0 : 0 ≤ cutoff (r / R) := Real.smoothTransition.nonneg _
  have hcut1 : cutoff (r / R) ≤ 1 := Real.smoothTransition.le_one _
  have he : monopoleInnerRadialProfile R r =
      (1 - cutoff (r / R)) * monopoleRadialProfile r := by
    unfold monopoleInnerRadialProfile monopoleInnerProfile monopoleRadialProfile
    ring
  rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hcut1)]
  calc
    (1 - cutoff (r / R)) * |monopoleRadialProfile r| ≤
        1 * |monopoleRadialProfile r| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ monopoleRadialBoundConstant := by
      simpa only [one_mul] using monopoleRadialProfile_abs_le hr

/-- The explicit bound depends only on the fixed actual monopole construction. -/
def monopoleLocalCubicBoundConstant : ℝ :=
  3 * monopoleRadialBoundConstant + 3 * monopoleRadialBoundConstant ^ 2 +
    monopoleRadialBoundConstant ^ 3

theorem monopoleLocalCubicBoundConstant_pos : 0 < monopoleLocalCubicBoundConstant := by
  have hB := monopoleRadialBoundConstant_pos
  unfold monopoleLocalCubicBoundConstant
  positivity

/-- The genuine local cubic perturbation has a uniform quadratic amplitude error.
This controls the local term; it makes no assertion about the nonlocal Hartree remainder. -/
theorem monopoleInnerRadialProfile_local_cubic_abs_le
    {R c r : ℝ} (hr : 0 < r) (hc : |c| ≤ 1) :
    |c * (bubble r + c * monopoleInnerRadialProfile R r) ^ 3 -
      c * bubble r ^ 3| ≤ monopoleLocalCubicBoundConstant * c ^ 2 := by
  have hB := monopoleRadialBoundConstant_pos.le
  have hX := monopoleInnerRadialProfile_abs_le (R := R) hr
  have hW : |bubble r| ≤ 1 := by
    have hs : 1 ≤ Real.sqrt (1 + r ^ 2) := by
      have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + r ^ 2 by nlinarith [sq_nonneg r])
      simpa only [Real.sqrt_one] using hh
    unfold bubble
    rw [abs_of_nonneg (by positivity)]
    exact (inv_le_one₀ (by positivity)).2 hs
  have hb : |localCubicQuadraticRemainder bubble (monopoleInnerRadialProfile R) c r| ≤
      monopoleLocalCubicBoundConstant := by
    unfold localCubicQuadraticRemainder
    calc
      |3 * bubble r ^ 2 * monopoleInnerRadialProfile R r +
          3 * c * bubble r * monopoleInnerRadialProfile R r ^ 2 +
          c ^ 2 * monopoleInnerRadialProfile R r ^ 3| ≤
          |3 * bubble r ^ 2 * monopoleInnerRadialProfile R r| +
          |3 * c * bubble r * monopoleInnerRadialProfile R r ^ 2| +
          |c ^ 2 * monopoleInnerRadialProfile R r ^ 3| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = 3 * |bubble r| ^ 2 * |monopoleInnerRadialProfile R r| +
          3 * |c| * |bubble r| * |monopoleInnerRadialProfile R r| ^ 2 +
          |c| ^ 2 * |monopoleInnerRadialProfile R r| ^ 3 := by
        simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 3 * (1 : ℝ) ^ 2 * monopoleRadialBoundConstant +
          3 * 1 * 1 * monopoleRadialBoundConstant ^ 2 +
          1 ^ 2 * monopoleRadialBoundConstant ^ 3 := by
        gcongr
      _ = monopoleLocalCubicBoundConstant := by
        unfold monopoleLocalCubicBoundConstant
        ring
  rw [local_cubic_first_order_exact bubble (monopoleInnerRadialProfile R) c r,
    add_sub_cancel_left, abs_mul, abs_of_nonneg (sq_nonneg c)]
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg c)).trans_eq (mul_comm _ _)

end HBL.Modulation.Monopole
