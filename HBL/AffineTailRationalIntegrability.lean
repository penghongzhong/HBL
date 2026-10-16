import HBL.AffineTailHPlusScalarBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Two absolutely integrable rational kernels used after the principal-value
decomposition.  The first integral is already a verified Mathlib result.
The second kernel is dominated by the first, so it is also Lebesgue
integrable, not merely assigned a formal integral.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- First elementary integral, as a concrete half-line equality. -/
theorem first_rational_integral :
    (∫ x in Ioi (0 : ℝ), (1 + x ^ 2)⁻¹) = Real.pi / 2 := by
  simpa only [Real.arctan_zero, sub_zero] using
    (integral_Ioi_inv_one_add_sq (i := (0 : ℝ)))

/-- The second rational kernel is bounded pointwise by the first. -/
theorem inv_sq_rational_norm_le (x : ℝ) :
    ‖((1 + x ^ 2) ^ 2)⁻¹‖ ≤ ‖(1 + x ^ 2)⁻¹‖ := by
  have hp : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hle : (1 + x ^ 2 : ℝ) ≤ (1 + x ^ 2) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  have hInv := one_div_le_one_div_of_le hp hle
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos hp 2)),
    abs_of_pos (inv_pos.mpr hp)]
  simpa only [one_div] using hInv

/-- The rational kernel with squared denominator is genuinely L1. -/
theorem second_rational_integrable :
    Integrable (fun x : ℝ => ((1 + x ^ 2) ^ 2)⁻¹) := by
  have hc : Continuous (fun x : ℝ => 1 + x ^ 2) := by fun_prop
  have hne (x : ℝ) : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have hd : Continuous (fun x : ℝ => ((1 + x ^ 2) ^ 2)⁻¹) :=
    (hc.pow 2).inv₀ (fun x => pow_ne_zero 2 (hne x))
  exact Integrable.mono' integrable_inv_one_add_sq
    hd.aestronglyMeasurable
    (ae_of_all _ (fun x => by
      have hp : (0 : ℝ) < 1 + x ^ 2 := by positivity
      simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
        using inv_sq_rational_norm_le x))

/-- This gives the required integrability on the positive half-line. -/
theorem second_rational_integrableOn :
    IntegrableOn (fun x : ℝ => ((1 + x ^ 2) ^ 2)⁻¹) (Ioi 0) :=
  second_rational_integrable.integrableOn

end HBL.Modulation.AffineTail
