import HBL.RadialHartreeDomination

/-! Actual cubic factors needed to assemble the complete radial Hartree Taylor error. -/

noncomputable section
namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The actual amplitude-perturbed inner profile. -/
def monopolePerturbedRadialProfile (R c r : ℝ) : ℝ :=
  bubble r + c * monopoleInnerRadialProfile R r

/-- Bound for the cubic first difference after its amplitude is extracted. -/
def monopoleOuterCubicDifferenceConstant : ℝ :=
  3 * monopoleRadialBoundConstant + 3 * monopoleRadialBoundConstant ^ 2 +
    monopoleRadialBoundConstant ^ 3

/-- Bound for the cubic second-order Taylor polynomial. -/
def monopoleOuterCubicTaylorConstant : ℝ :=
  3 * monopoleRadialBoundConstant ^ 2 + monopoleRadialBoundConstant ^ 3

theorem monopolePerturbedRadialProfile_abs_le {R c r : ℝ}
    (hr : 0 < r) (hc : |c| ≤ 1) :
    |monopolePerturbedRadialProfile R c r| ≤ 1 + monopoleRadialBoundConstant := by
  unfold monopolePerturbedRadialProfile
  calc
    |bubble r + c * monopoleInnerRadialProfile R r| ≤
        |bubble r| + |c| * |monopoleInnerRadialProfile R r| := by
      simpa only [abs_mul] using abs_add_le (bubble r) (c * monopoleInnerRadialProfile R r)
    _ ≤ 1 + 1 * monopoleRadialBoundConstant := by
      gcongr
      · exact bubble_abs_le_one r
      · exact monopoleInnerRadialProfile_abs_le hr
    _ = _ := by ring

/-- The actual cubic first difference has an amplitude-uniform linear bound. -/
theorem monopoleOuterCubic_difference_abs_le {R c r : ℝ}
    (hr : 0 < r) (hc : |c| ≤ 1) :
    |monopolePerturbedRadialProfile R c r ^ 3 - bubble r ^ 3| ≤
      monopoleOuterCubicDifferenceConstant * |c| := by
  have hW := bubble_abs_le_one r
  have hX := monopoleInnerRadialProfile_abs_le (R := R) hr
  have hB := monopoleRadialBoundConstant_pos.le
  have he : monopolePerturbedRadialProfile R c r ^ 3 - bubble r ^ 3 =
      c * (3 * bubble r ^ 2 * monopoleInnerRadialProfile R r +
        3 * c * bubble r * monopoleInnerRadialProfile R r ^ 2 +
        c ^ 2 * monopoleInnerRadialProfile R r ^ 3) := by
    unfold monopolePerturbedRadialProfile
    ring
  have hp : |3 * bubble r ^ 2 * monopoleInnerRadialProfile R r +
      3 * c * bubble r * monopoleInnerRadialProfile R r ^ 2 +
      c ^ 2 * monopoleInnerRadialProfile R r ^ 3| ≤ monopoleOuterCubicDifferenceConstant := by
    calc
      _ ≤ |3 * bubble r ^ 2 * monopoleInnerRadialProfile R r| +
          |3 * c * bubble r * monopoleInnerRadialProfile R r ^ 2| +
          |c ^ 2 * monopoleInnerRadialProfile R r ^ 3| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = 3 * |bubble r| ^ 2 * |monopoleInnerRadialProfile R r| +
          3 * |c| * |bubble r| * |monopoleInnerRadialProfile R r| ^ 2 +
          |c| ^ 2 * |monopoleInnerRadialProfile R r| ^ 3 := by
        simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 3 * (1 : ℝ) ^ 2 * monopoleRadialBoundConstant +
          3 * 1 * 1 * monopoleRadialBoundConstant ^ 2 +
          1 ^ 2 * monopoleRadialBoundConstant ^ 3 := by gcongr
      _ = monopoleOuterCubicDifferenceConstant := by
        unfold monopoleOuterCubicDifferenceConstant
        ring
  rw [he, abs_mul]
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg c)).trans_eq (mul_comm _ _)

/-- The actual cubic Taylor remainder has a radius-uniform quadratic bound. -/
theorem monopoleOuterCubic_taylor_abs_le {R c r : ℝ}
    (hr : 0 < r) (hc : |c| ≤ 1) :
    |monopolePerturbedRadialProfile R c r ^ 3 - bubble r ^ 3 -
      3 * c * bubble r ^ 2 * monopoleInnerRadialProfile R r| ≤
      monopoleOuterCubicTaylorConstant * c ^ 2 := by
  have hW := bubble_abs_le_one r
  have hX := monopoleInnerRadialProfile_abs_le (R := R) hr
  have hB := monopoleRadialBoundConstant_pos.le
  have he : monopolePerturbedRadialProfile R c r ^ 3 - bubble r ^ 3 -
      3 * c * bubble r ^ 2 * monopoleInnerRadialProfile R r =
      c ^ 2 * (3 * bubble r * monopoleInnerRadialProfile R r ^ 2 +
        c * monopoleInnerRadialProfile R r ^ 3) := by
    unfold monopolePerturbedRadialProfile
    ring
  have hp : |3 * bubble r * monopoleInnerRadialProfile R r ^ 2 +
      c * monopoleInnerRadialProfile R r ^ 3| ≤ monopoleOuterCubicTaylorConstant := by
    calc
      _ ≤ |3 * bubble r * monopoleInnerRadialProfile R r ^ 2| +
          |c * monopoleInnerRadialProfile R r ^ 3| := abs_add_le _ _
      _ = 3 * |bubble r| * |monopoleInnerRadialProfile R r| ^ 2 +
          |c| * |monopoleInnerRadialProfile R r| ^ 3 := by
        simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 3 * 1 * monopoleRadialBoundConstant ^ 2 +
          1 * monopoleRadialBoundConstant ^ 3 := by gcongr
      _ = monopoleOuterCubicTaylorConstant := by
        unfold monopoleOuterCubicTaylorConstant
        ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg c)]
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg c)).trans_eq (mul_comm _ _)

end HBL.Modulation.Monopole
