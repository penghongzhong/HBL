import HBL.MonopoleLocalCubicBound

/-! The actual compactly supported fourth-power density remainder. -/

noncomputable section
open MeasureTheory

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The actual fourth-power density with its constant and linear terms removed. -/
def monopoleHartreeDensityRemainder (R c rho : ℝ) : ℝ :=
  (bubble rho + c * monopoleInnerRadialProfile R rho) ^ 4 - bubble rho ^ 4 -
    4 * c * bubble rho ^ 3 * monopoleInnerRadialProfile R rho

/-- The exact polynomial after extracting the quadratic amplitude factor. -/
def monopoleHartreeDensityPolynomial (R c rho : ℝ) : ℝ :=
  6 * bubble rho ^ 2 * monopoleInnerRadialProfile R rho ^ 2 +
    4 * c * bubble rho * monopoleInnerRadialProfile R rho ^ 3 +
    c ^ 2 * monopoleInnerRadialProfile R rho ^ 4

def monopoleHartreeDensityBoundConstant : ℝ :=
  6 * monopoleRadialBoundConstant ^ 2 + 4 * monopoleRadialBoundConstant ^ 3 +
    monopoleRadialBoundConstant ^ 4

theorem monopoleHartreeDensityRemainder_eq_mul_polynomial (R c rho : ℝ) :
    monopoleHartreeDensityRemainder R c rho =
      c ^ 2 * monopoleHartreeDensityPolynomial R c rho := by
  unfold monopoleHartreeDensityRemainder monopoleHartreeDensityPolynomial
  ring

/-- All factors are actual measurable profiles, including the total radial quotient. -/
theorem monopoleHartreeDensityRemainder_measurable (R c : ℝ) :
    Measurable (monopoleHartreeDensityRemainder R c) := by
  have hc : Continuous (fun rho : ℝ => 1 - cutoff (rho / R)) :=
    continuous_const.sub
      (cutoff_contDiff_infty.continuous.comp (continuous_id.div_const R))
  have hX : Measurable (monopoleInnerRadialProfile R) := by
    exact (hc.mul monopoleProfile_continuous).measurable.div measurable_id
  have hW : Measurable bubble := bubble_contDiff_infty.continuous.measurable
  exact (((hW.add (hX.const_mul c)).pow_const 4).sub (hW.pow_const 4)).sub
    (((hW.pow_const 3).const_mul (4 * c)).mul hX)

/-- The nonlinear density remainder vanishes outside the actual inner truncation. -/
theorem monopoleHartreeDensityRemainder_zero_of_two_mul_le
    {R c rho : ℝ} (hR : 0 < R) (hsep : 2 * R ≤ rho) :
    monopoleHartreeDensityRemainder R c rho = 0 := by
  have hcut := cutoff_one_of_two_le (rho / R) ((le_div_iff₀ hR).mpr hsep)
  have hx : monopoleInnerRadialProfile R rho = 0 := by
    simp only [monopoleInnerRadialProfile, monopoleInnerProfile, hcut,
      sub_self, zero_mul, zero_div]
  simp only [monopoleHartreeDensityRemainder, hx, mul_zero, add_zero, sub_self]

/-- The extracted quadratic polynomial is uniformly bounded in the cutoff radius. -/
theorem monopoleHartreeDensityPolynomial_abs_le
    {R c rho : ℝ} (hrho : 0 < rho) (hc : |c| ≤ 1) :
    |monopoleHartreeDensityPolynomial R c rho| ≤ monopoleHartreeDensityBoundConstant := by
  have hB := monopoleRadialBoundConstant_pos.le
  have hX := monopoleInnerRadialProfile_abs_le (R := R) hrho
  have hW : |bubble rho| ≤ 1 := by
    have hs : 1 ≤ Real.sqrt (1 + rho ^ 2) := by
      have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + rho ^ 2 by nlinarith [sq_nonneg rho])
      simpa only [Real.sqrt_one] using hh
    unfold bubble
    rw [abs_of_nonneg (by positivity)]
    exact (inv_le_one₀ (by positivity)).2 hs
  unfold monopoleHartreeDensityPolynomial
  calc
    |6 * bubble rho ^ 2 * monopoleInnerRadialProfile R rho ^ 2 +
        4 * c * bubble rho * monopoleInnerRadialProfile R rho ^ 3 +
        c ^ 2 * monopoleInnerRadialProfile R rho ^ 4| ≤
        |6 * bubble rho ^ 2 * monopoleInnerRadialProfile R rho ^ 2| +
        |4 * c * bubble rho * monopoleInnerRadialProfile R rho ^ 3| +
        |c ^ 2 * monopoleInnerRadialProfile R rho ^ 4| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 6 * |bubble rho| ^ 2 * |monopoleInnerRadialProfile R rho| ^ 2 +
        4 * |c| * |bubble rho| * |monopoleInnerRadialProfile R rho| ^ 3 +
        |c| ^ 2 * |monopoleInnerRadialProfile R rho| ^ 4 := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ 6 * (1 : ℝ) ^ 2 * monopoleRadialBoundConstant ^ 2 +
        4 * 1 * 1 * monopoleRadialBoundConstant ^ 3 +
        1 ^ 2 * monopoleRadialBoundConstant ^ 4 := by
      gcongr
    _ = monopoleHartreeDensityBoundConstant := by
      unfold monopoleHartreeDensityBoundConstant
      ring

/-- A true uniform quadratic bound for the actual fourth-power density remainder. -/
theorem monopoleHartreeDensityRemainder_abs_le
    {R c rho : ℝ} (hrho : 0 < rho) (hc : |c| ≤ 1) :
    |monopoleHartreeDensityRemainder R c rho| ≤
      monopoleHartreeDensityBoundConstant * c ^ 2 := by
  rw [monopoleHartreeDensityRemainder_eq_mul_polynomial, abs_mul,
    abs_of_nonneg (sq_nonneg c)]
  exact (mul_le_mul_of_nonneg_left
    (monopoleHartreeDensityPolynomial_abs_le hrho hc) (sq_nonneg c)).trans_eq (mul_comm _ _)

end HBL.Modulation.Monopole
