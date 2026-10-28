import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The L2-Linfinity interpolation exponent used by the HBL graph source

The noncompact kernel split requires an operator-valued density derivative
in L^(25/8).  For the fixed smooth bubble/background coefficients this
follows directly from L2 and an essential Linfinity bound; no finite-measure
hypothesis and no compact support are used.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HBL.RegularRadiation.GraphInterpolation

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E]

/-- Exact exponent needed by the near-kernel Holder pair 25/17--25/8. -/
theorem memLp_twentyfive_eighths_of_two_aeBound
    (μ : Measure α) (f : α → E)
    (hf : Continuous f)
    (hf2 : MemLp f 2 μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) :
    MemLp f (ENNReal.ofReal (25 / 8 : ℝ)) μ := by
  have hp0 : ENNReal.ofReal (25 / 8 : ℝ) ≠ 0 := by norm_num
  have hpt : ENNReal.ofReal (25 / 8 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [← integrable_norm_rpow_iff hf.aestronglyMeasurable hp0 hpt,
    ENNReal.toReal_ofReal (by norm_num : 0 ≤ (25 / 8 : ℝ))]
  have h2 : Integrable (fun x => ‖f x‖ ^ (2 : ℕ)) μ :=
    hf2.integrable_norm_pow (by norm_num)
  have hmajor :
      Integrable (fun x => M ^ (9 / 8 : ℝ) * ‖f x‖ ^ (2 : ℕ)) μ :=
    h2.const_mul (M ^ (9 / 8 : ℝ))
  have hmeas :
      AEStronglyMeasurable (fun x => ‖f x‖ ^ (25 / 8 : ℝ)) μ :=
    (Continuous.rpow_const hf.norm
      (fun _ => Or.inr (by norm_num : 0 ≤ (25 / 8 : ℝ)))).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [hbound] with x hx
  have hbase :
      ‖f x‖ ^ (9 / 8 : ℝ) ≤ M ^ (9 / 8 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hx (by norm_num)
  have hfac :
      ‖f x‖ ^ (9 / 8 : ℝ) * ‖f x‖ ^ (2 : ℕ) ≤
        M ^ (9 / 8 : ℝ) * ‖f x‖ ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right hbase (sq_nonneg ‖f x‖)
  have hsplit :
      ‖f x‖ ^ (25 / 8 : ℝ) =
        ‖f x‖ ^ (9 / 8 : ℝ) * ‖f x‖ ^ (2 : ℕ) := by
    calc
      ‖f x‖ ^ (25 / 8 : ℝ) =
          ‖f x‖ ^ ((9 / 8 : ℝ) + 2) := by norm_num
      _ = ‖f x‖ ^ (9 / 8 : ℝ) * ‖f x‖ ^ (2 : ℝ) :=
        Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)
      _ = _ := by rw [Real.rpow_natCast]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    hsplit, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hM _) (sq_nonneg ‖f x‖))]
  exact hfac

#print axioms memLp_twentyfive_eighths_of_two_aeBound

end HBL.RegularRadiation.GraphInterpolation
