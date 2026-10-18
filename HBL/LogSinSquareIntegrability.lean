import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Square-integrability at the logarithmic endpoints of `log (sin x)`.
-/

noncomputable section

open Set MeasureTheory

namespace HBL

theorem log_sq_le_inv_sqrt
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ^ 2 ≤ 16 * x ^ (-(1 / 2 : ℝ)) := by
  have hbpos : 0 < x ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hx0 _
  have hraw := Real.abs_log_mul_self_rpow_lt x (1 / 4 : ℝ)
    hx0 hx1 (by norm_num)
  have habs : |Real.log x| * x ^ (1 / 4 : ℝ) < 4 := by
    rw [abs_mul, abs_of_pos hbpos] at hraw
    norm_num at hraw
    exact hraw
  have hquot : |Real.log x| < 4 / x ^ (1 / 4 : ℝ) :=
    (lt_div_iff₀ hbpos).2 habs
  have hsquare : |Real.log x| ^ 2 ≤
      (4 / x ^ (1 / 4 : ℝ)) ^ 2 := by
    nlinarith [abs_nonneg (Real.log x)]
  have hpower : (4 / x ^ (1 / 4 : ℝ)) ^ 2 =
      16 * x ^ (-(1 / 2 : ℝ)) := by
    rw [div_pow]
    have hsq : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hx0.le]
      norm_num
    rw [hsq]
    rw [Real.rpow_neg hx0.le]
    norm_num
    ring
  rw [sq_abs, hpower] at hsquare
  exact hsquare

theorem integrableOn_log_sq_Ioo_zero_one :
    IntegrableOn (fun x : ℝ => Real.log x ^ 2) (Ioo 0 1) := by
  have hpow : IntegrableOn
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)
  refine (hpow.const_mul 16).mono' ?_ ?_
  · exact (Real.measurable_log.pow_const 2).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact log_sq_le_inv_sqrt hx.1 hx.2.le

theorem integrableOn_sin_inv_sqrt_Ioo_zero_pi_half :
    IntegrableOn (fun x : ℝ => Real.sin x ^ (-(1 / 2 : ℝ)))
      (Ioo 0 (Real.pi / 2)) := by
  have hpow : IntegrableOn
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioo 0 (Real.pi / 2)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by positivity)).2 (by norm_num)
  have hc : 0 ≤ (2 / Real.pi) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  refine (hpow.const_mul ((2 / Real.pi) ^ (-(1 / 2 : ℝ)))).mono' ?_ ?_
  · refine
      (Real.continuous_sin.continuousOn.rpow_const ?_).aestronglyMeasurable
        measurableSet_Ioo
    intro x hx
    left
    exact (Real.sin_pos_of_pos_of_lt_pi hx.1 (by
      nlinarith [hx.2, Real.pi_pos])).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hlinpos : 0 < 2 / Real.pi * x := mul_pos (by positivity) hx.1
    have hsinpos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx.1 (by nlinarith [hx.2, Real.pi_pos])
    have hle : Real.sin x ^ (-(1 / 2 : ℝ)) ≤
        (2 / Real.pi * x) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlinpos
        (Real.mul_le_sin hx.1.le hx.2.le) (by norm_num)
    rw [Real.mul_rpow (by positivity) hx.1.le] at hle
    simpa only [Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hsinpos _),
      abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg _ _))] using hle

theorem integrableOn_sin_inv_sqrt_Ioo_zero_pi :
    IntegrableOn (fun x : ℝ => Real.sin x ^ (-(1 / 2 : ℝ)))
      (Ioo 0 Real.pi) := by
  have hleft : IntervalIntegrable
      (fun x : ℝ => Real.sin x ^ (-(1 / 2 : ℝ))) volume
      0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
    exact integrableOn_sin_inv_sqrt_Ioo_zero_pi_half
  have hright : IntervalIntegrable
      (fun x : ℝ => Real.sin x ^ (-(1 / 2 : ℝ))) volume
      (Real.pi / 2) Real.pi := by
    have hreflected := (hleft.comp_sub_left Real.pi).symm
    convert hreflected using 1
    · funext x
      rw [Real.sin_pi_sub]
    · ring
    · ring
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
  exact hleft.trans hright

theorem integrableOn_log_sin_sq_Ioo_zero_pi :
    IntegrableOn (fun x : ℝ => Real.log (Real.sin x) ^ 2)
      (Ioo 0 Real.pi) := by
  refine (integrableOn_sin_inv_sqrt_Ioo_zero_pi.const_mul 16).mono' ?_ ?_
  · have hm : Measurable (fun x : ℝ => Real.log (Real.sin x) ^ 2) :=
      (Real.measurable_log.comp Real.continuous_sin.measurable).pow_const 2
    exact hm.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact log_sq_le_inv_sqrt
      (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2) (Real.sin_le_one x)

end HBL
