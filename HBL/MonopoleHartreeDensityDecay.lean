import HBL.MonopoleHartreeDensity
import HBL.MonopoleQuadraticCutoff

/-! A radius-independent decaying majorant for the actual quartic density error. -/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail

/-- The constant supplied by the actual radial bound and the chosen cutoff. -/
def monopoleHartreeDensityDecayConstant : ℝ :=
  6 * monopoleRadialBoundConstant ^ 2 + 36 * monopoleRadialBoundConstant ^ 3 +
    81 * monopoleRadialBoundConstant ^ 4

private theorem amplitude_le_nine_bubble {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r)
    (hcut : r ≤ 2 * monopoleQuadraticRadius c) :
    |c| ≤ 9 * bubble r := by
  have hcr : |c| * r ≤ 8 := by
    unfold monopoleQuadraticRadius at hcut
    have hh := mul_le_mul_of_nonneg_left hcut hc.le
    field_simp at hh
    nlinarith
  have hs : Real.sqrt (1 + r ^ 2) ≤ 1 + r := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hh : |c| * Real.sqrt (1 + r ^ 2) ≤ 9 := by
    calc
      |c| * Real.sqrt (1 + r ^ 2) ≤ |c| * (1 + r) :=
        mul_le_mul_of_nonneg_left hs hc.le
      _ ≤ 9 := by nlinarith
  unfold bubble
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < Real.sqrt (1 + r ^ 2))]
  exact hh

/-- The genuine quartic Taylor density has a uniform decaying quadratic majorant. -/
theorem monopoleHartreeDensityRemainder_weighted_abs_le {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r) :
    |monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c r| ≤
      monopoleHartreeDensityDecayConstant * c ^ 2 * bubble r ^ 2 := by
  have hB := monopoleRadialBoundConstant_pos.le
  have hW : 0 ≤ bubble r := by unfold bubble; positivity
  have hR : 0 < monopoleQuadraticRadius c := by
    unfold monopoleQuadraticRadius
    positivity
  by_cases hfar : 2 * monopoleQuadraticRadius c ≤ r
  · rw [monopoleHartreeDensityRemainder_zero_of_two_mul_le hR hfar, abs_zero]
    unfold monopoleHartreeDensityDecayConstant
    positivity
  have hcw := amplitude_le_nine_bubble hc hc1 hr (le_of_not_ge hfar)
  have hX := monopoleInnerRadialProfile_abs_le (R := monopoleQuadraticRadius c) hr
  have hp : |monopoleHartreeDensityPolynomial (monopoleQuadraticRadius c) c r| ≤
      monopoleHartreeDensityDecayConstant * bubble r ^ 2 := by
    unfold monopoleHartreeDensityPolynomial
    calc
      |6 * bubble r ^ 2 * monopoleInnerRadialProfile (monopoleQuadraticRadius c) r ^ 2 +
          4 * c * bubble r * monopoleInnerRadialProfile (monopoleQuadraticRadius c) r ^ 3 +
          c ^ 2 * monopoleInnerRadialProfile (monopoleQuadraticRadius c) r ^ 4| ≤
          |6 * bubble r ^ 2 * monopoleInnerRadialProfile (monopoleQuadraticRadius c) r ^ 2| +
          |4 * c * bubble r * monopoleInnerRadialProfile (monopoleQuadraticRadius c) r ^ 3| +
          |c ^ 2 * monopoleInnerRadialProfile (monopoleQuadraticRadius c) r ^ 4| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = 6 * bubble r ^ 2 * |monopoleInnerRadialProfile (monopoleQuadraticRadius c) r| ^ 2 +
          4 * |c| * bubble r * |monopoleInnerRadialProfile (monopoleQuadraticRadius c) r| ^ 3 +
          |c| ^ 2 * |monopoleInnerRadialProfile (monopoleQuadraticRadius c) r| ^ 4 := by
        simp only [abs_mul, abs_pow, abs_of_nonneg hW,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      _ ≤ 6 * bubble r ^ 2 * monopoleRadialBoundConstant ^ 2 +
          4 * (9 * bubble r) * bubble r * monopoleRadialBoundConstant ^ 3 +
          (9 * bubble r) ^ 2 * monopoleRadialBoundConstant ^ 4 := by
        gcongr
      _ = monopoleHartreeDensityDecayConstant * bubble r ^ 2 := by
        unfold monopoleHartreeDensityDecayConstant
        ring
  rw [monopoleHartreeDensityRemainder_eq_mul_polynomial, abs_mul,
    abs_of_nonneg (sq_nonneg c)]
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg c)).trans_eq (by ring)

end HBL.Modulation.Monopole
