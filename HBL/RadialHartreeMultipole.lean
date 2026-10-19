import HBL.RadialHartreePotential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual separated exterior Riesz potentials and their center mass.
The exterior piece is an explicit split of a density, not a support assumption
on a radiation field. The original totalized radial potential is not assigned
its physical center value at radius zero. -/

noncomputable section
open Set MeasureTheory

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- A cubic remainder for the actual logarithm on a separated radial row. -/
theorem radialLog_cubic_remainder {t : ℝ} (ht : 0 ≤ t) (htop : t ≤ 1 / 2) :
    0 ≤ Real.log ((1 + t) / (1 - t)) - 2 * t ∧
      Real.log ((1 + t) / (1 - t)) - 2 * t ≤ 2 * t ^ 3 := by
  have ht1 : t < 1 := by linarith
  have hlo := Real.sum_range_le_log_div ht ht1 1
  have hup := Real.log_div_le_sum_range_add ht ht1 2
  norm_num [Finset.sum_range_succ] at hlo hup
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr htop)]
  have hd : 0 < 1 - t ^ 2 := by linarith
  have hrem : t ^ 5 / (1 - t ^ 2) ≤ t ^ 3 / 3 := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg (pow_nonneg ht 3) (show 0 ≤ 1 - 4 * t ^ 2 by linarith)]
  constructor
  · linarith
  · nlinarith [pow_nonneg ht 3]

/-- Subtracting the actual center kernel leaves a nonnegative cubic radial row. -/
theorem radialHartreeRow_center_remainder {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho) (hsep : 2 * r ≤ rho) :
    0 ≤ rho * hartreeRadialLog r rho - 2 * r ∧
      rho * hartreeRadialLog r rho - 2 * r ≤ 2 * r ^ 3 / rho ^ 2 := by
  have hratio : r / rho ≤ 1 / 2 := (div_le_iff₀ hrho).2 (by linarith)
  have hh := radialLog_cubic_remainder (div_nonneg hr.le hrho.le) hratio
  have hlog : hartreeRadialLog r rho = Real.log ((1 + r / rho) / (1 - r / rho)) := by
    unfold hartreeRadialLog
    rw [abs_of_neg (show r - rho < 0 by linarith)]
    congr 1
    field_simp [ne_of_lt (show r - rho < 0 by linarith),
      ne_of_gt (show 0 < rho - r by linarith)]
    ring
  rw [hlog]
  have hid : rho * (Real.log ((1 + r / rho) / (1 - r / rho)) - 2 * (r / rho)) =
      rho * Real.log ((1 + r / rho) / (1 - r / rho)) - 2 * r := by
    field_simp
  constructor
  · rw [← hid]
    exact mul_nonneg hrho.le hh.1
  · calc
      rho * Real.log ((1 + r / rho) / (1 - r / rho)) - 2 * r ≤
          rho * (2 * (r / rho) ^ 3) := by
        rw [← hid]
        exact mul_le_mul_of_nonneg_left hh.2 hrho.le
      _ = 2 * r ^ 3 / rho ^ 2 := by field_simp

/-- The exterior part of the actual normalized radial potential. -/
def radialHartreeExteriorPotential (F : ℝ → ℝ) (R r : ℝ) : ℝ :=
  (2 * Real.pi * hartreeKappa / r) *
    ∫ rho in Ioi R, rho * hartreeRadialLog r rho * F rho

/-- The genuine exterior center mass, separately defined from total division at zero. -/
def radialHartreeExteriorCenter (F : ℝ → ℝ) (R : ℝ) : ℝ :=
  4 * Real.pi * hartreeKappa * ∫ rho in Ioi R, F rho

/-- The exterior operator is exactly the existing radial potential of the
corresponding indicator density. -/
theorem radialHartreeExteriorPotential_eq_indicator (F : ℝ → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (r : ℝ) :
    radialHartreeExteriorPotential F R r =
      radialHartreePotential ((Ioi R).indicator F) r := by
  unfold radialHartreeExteriorPotential radialHartreePotential
  congr 1
  symm
  have hfun : (fun rho => rho * hartreeRadialLog r rho * (Ioi R).indicator F rho) =
      (Ioi R).indicator (fun rho => rho * hartreeRadialLog r rho * F rho) := by
    funext rho
    by_cases hh : rho ∈ Ioi R
    · simp [hh]
    · simp [hh]
  rw [hfun, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (show Ioi R ⊆ Ioi (0 : ℝ) from fun rho hrho => hR.trans_lt hrho)]

/-- An integrable actual exterior density has an absolutely convergent potential;
its center error is quadratic, controlled by a genuine weighted density moment.
No exterior support is imposed on the unsplit density. -/
theorem radialHartreeExteriorPotential_quadratic_center
    (F : ℝ → ℝ) (hf : Measurable F) {R r : ℝ}
    (hF : IntegrableOn F (Ioi R)) (hR : 0 < R) (hr : 0 < r)
    (hsep : 2 * r ≤ R) :
    IntegrableOn (fun rho => |F rho| / rho ^ 2) (Ioi R) ∧
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi R) ∧
    |radialHartreeExteriorPotential F R r - radialHartreeExteriorCenter F R| ≤
      4 * Real.pi * hartreeKappa * r ^ 2 *
        ∫ rho in Ioi R, |F rho| / rho ^ 2 := by
  have hwpoint : ∀ rho ∈ Ioi R, |F rho| / rho ^ 2 ≤ R⁻¹ ^ 2 * |F rho| := by
    intro rho hrho
    have hden : R ^ 2 ≤ rho ^ 2 := pow_le_pow_left₀ hR.le hrho.le 2
    calc
      |F rho| / rho ^ 2 ≤ |F rho| / R ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hR) hden
      _ = R⁻¹ ^ 2 * |F rho| := by ring
  have hfabs : Measurable (fun rho => |F rho|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hw : IntegrableOn (fun rho => |F rho| / rho ^ 2) (Ioi R) := by
    apply (hF.abs.const_mul (R⁻¹ ^ 2)).mono'
      ((hfabs.div (measurable_id.pow_const 2)).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    change ‖|F rho| / rho ^ 2‖ ≤ R⁻¹ ^ 2 * |F rho|
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (abs_nonneg (F rho)) (sq_nonneg rho))]
    exact hwpoint rho hrho
  let Q : ℝ → ℝ := fun rho => (rho * hartreeRadialLog r rho - 2 * r) * F rho
  have hQpoint : ∀ rho ∈ Ioi R, |Q rho| ≤ 2 * r ^ 3 * (|F rho| / rho ^ 2) := by
    intro rho hrho
    have hrem := radialHartreeRow_center_remainder hr (hR.trans hrho) (hsep.trans hrho.le)
    dsimp [Q]
    rw [abs_mul, abs_of_nonneg hrem.1]
    calc
      (rho * hartreeRadialLog r rho - 2 * r) * |F rho| ≤
          (2 * r ^ 3 / rho ^ 2) * |F rho| :=
        mul_le_mul_of_nonneg_right hrem.2 (abs_nonneg _)
      _ = 2 * r ^ 3 * (|F rho| / rho ^ 2) := by ring
  have hlogmeas : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hQmeas : Measurable Q :=
    ((measurable_id.mul hlogmeas).sub measurable_const).mul hf
  have hQ : IntegrableOn Q (Ioi R) := by
    apply (hw.const_mul (2 * r ^ 3)).mono' hQmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [Real.norm_eq_abs]
    exact hQpoint rho hrho
  have hrow : IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi R) := by
    convert hQ.add (hF.const_mul (2 * r)) using 1
    funext rho
    dsimp [Q]
    ring
  have hQI : |∫ rho in Ioi R, Q rho| ≤
      2 * r ^ 3 * ∫ rho in Ioi R, |F rho| / rho ^ 2 := by
    calc
      |∫ rho in Ioi R, Q rho| ≤ ∫ rho in Ioi R, |Q rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi R, 2 * r ^ 3 * (|F rho| / rho ^ 2) := by
        apply integral_mono_ae hQ.abs (hw.const_mul (2 * r ^ 3))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hQpoint rho hrho
      _ = _ := by rw [integral_const_mul]
  have hfun : Q = fun rho => rho * hartreeRadialLog r rho * F rho - (2 * r) * F rho := by
    funext rho
    dsimp [Q]
    ring
  have hQeq : (∫ rho in Ioi R, Q rho) =
      (∫ rho in Ioi R, rho * hartreeRadialLog r rho * F rho) -
        (2 * r) * ∫ rho in Ioi R, F rho := by
    rw [hfun, integral_sub hrow (hF.const_mul (2 * r)), integral_const_mul]
  have heq : radialHartreeExteriorPotential F R r - radialHartreeExteriorCenter F R =
      (2 * Real.pi * hartreeKappa / r) * ∫ rho in Ioi R, Q rho := by
    unfold radialHartreeExteriorPotential radialHartreeExteriorCenter
    rw [hQeq]
    field_simp
    ring
  have hcoeff : 0 ≤ 2 * Real.pi * hartreeKappa / r := by
    unfold hartreeKappa
    positivity
  refine ⟨hw, hrow, ?_⟩
  rw [heq, abs_mul, abs_of_nonneg hcoeff]
  calc
    (2 * Real.pi * hartreeKappa / r) * |∫ rho in Ioi R, Q rho| ≤
        (2 * Real.pi * hartreeKappa / r) *
          (2 * r ^ 3 * ∫ rho in Ioi R, |F rho| / rho ^ 2) :=
      mul_le_mul_of_nonneg_left hQI hcoeff
    _ = _ := by field_simp; ring

/-- The separately defined center mass is the genuine positive-radius limit
of the actual exterior potential, despite the original total quotient at zero. -/
theorem radialHartreeExteriorPotential_tendsto_center
    (F : ℝ → ℝ) (hf : Measurable F) {R : ℝ}
    (hF : IntegrableOn F (Ioi R)) (hR : 0 < R) :
    Filter.Tendsto (radialHartreeExteriorPotential F R) (nhdsWithin 0 (Ioi 0))
      (nhds (radialHartreeExteriorCenter F R)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hlim : Filter.Tendsto
      (fun r : ℝ => 4 * Real.pi * hartreeKappa * r ^ 2 *
        ∫ rho in Ioi R, |F rho| / rho ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      nhdsWithin_le_nhds
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul] using
      ((hid.pow 2).const_mul (4 * Real.pi * hartreeKappa)).mul_const
        (∫ rho in Ioi R, |F rho| / rho ^ 2)
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) ?_ hlim
  have hnear : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), r < R / 2 :=
    (eventually_lt_nhds (show (0 : ℝ) < R / 2 by positivity)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with r hr htop
  rw [Real.dist_eq]
  exact (radialHartreeExteriorPotential_quadratic_center F hf hF hR hr
    (by linarith)).2.2

end HBL.Modulation.Monopole
