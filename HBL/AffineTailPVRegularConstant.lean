import HBL.AffineTailPVPrimitive

/-!
Exact constant of the nonsingular part of the Cauchy principal-value
decomposition. The remaining simple-pole component has symmetric
cutoff cancellation handled separately by AffineTailPVPrimitive.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- The two ordinary improper integrals combine to the exact rational
coefficient needed in the affine logarithmic integral. -/
theorem pv_regular_part_integral_value (r : ℝ) :
    (r ^ 2 / (1 + r ^ 2) ^ 2) *
        (∫ x in Ioi (0 : ℝ), (1 + x ^ 2)⁻¹) -
      (1 / (1 + r ^ 2)) *
        (∫ x in Ioi (0 : ℝ), ((1 + x ^ 2) ^ 2)⁻¹) =
      Real.pi * (r ^ 2 - 1) / (4 * (1 + r ^ 2) ^ 2) := by
  rw [first_rational_integral, second_rational_integral]
  have hne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hne]
  ring

end HBL.Modulation.AffineTail
