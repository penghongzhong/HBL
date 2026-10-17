import HBL.MonopoleTailCharge
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The logarithmic model used before the monopole Fredholm inversion has zero
real-channel threshold charge.  The model below is a globally smooth positive
extension of `log r`: it is zero for `r ≤ 1` and exactly `log r` for `r ≥ 2`.
Changing the interpolation on the compact annulus changes only the compact
normalization constant, not the threshold charge.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- Positive smooth radius equal to `1` in the core and to `r` in the far
field. -/
def smoothLogRadius (r : ℝ) : ℝ :=
  1 + cutoff r * (r - 1)

theorem smoothLogRadius_pos (r : ℝ) : 0 < smoothLogRadius r := by
  by_cases hr : r ≤ 1
  · simp [smoothLogRadius, cutoff_zero_of_le_one r hr]
  · have hc : 0 ≤ cutoff r := by
      unfold cutoff
      exact Real.smoothTransition.nonneg _
    have : 0 ≤ cutoff r * (r - 1) :=
      mul_nonneg hc (sub_nonneg.mpr (le_of_not_ge hr))
    unfold smoothLogRadius
    linarith

theorem smoothLogRadius_contDiff_infty :
    ContDiff ℝ ∞ smoothLogRadius := by
  unfold smoothLogRadius
  exact contDiff_const.add
    (cutoff_contDiff_infty.mul (contDiff_id.sub contDiff_const))

theorem smoothLogRadius_eq_one_of_le_one (r : ℝ) (hr : r ≤ 1) :
    smoothLogRadius r = 1 := by
  simp [smoothLogRadius, cutoff_zero_of_le_one r hr]

theorem smoothLogRadius_eq_self_of_two_le (r : ℝ) (hr : 2 ≤ r) :
    smoothLogRadius r = r := by
  simp [smoothLogRadius, cutoff_one_of_two_le r hr]

/-- The fixed smooth logarithmic tail model. -/
def monopoleLogModel (r : ℝ) : ℝ :=
  Real.log (smoothLogRadius r)

theorem monopoleLogModel_contDiff_infty :
    ContDiff ℝ ∞ monopoleLogModel := by
  unfold monopoleLogModel
  exact smoothLogRadius_contDiff_infty.log
    (fun r => ne_of_gt (smoothLogRadius_pos r))

theorem monopoleLogModel_zero_of_le_one (r : ℝ) (hr : r ≤ 1) :
    monopoleLogModel r = 0 := by
  rw [monopoleLogModel, smoothLogRadius_eq_one_of_le_one r hr,
    Real.log_one]

theorem monopoleLogModel_eq_log_of_two_le (r : ℝ) (hr : 2 ≤ r) :
    monopoleLogModel r = Real.log r := by
  rw [monopoleLogModel, smoothLogRadius_eq_self_of_two_le r hr]

theorem monopoleLogModel_nonneg (r : ℝ) :
    0 ≤ monopoleLogModel r := by
  unfold monopoleLogModel
  exact Real.log_nonneg (by
    unfold smoothLogRadius
    by_cases hr : r ≤ 1
    · simp [cutoff_zero_of_le_one r hr]
    · have hc : 0 ≤ cutoff r := by
        unfold cutoff
        exact Real.smoothTransition.nonneg _
      nlinarith [mul_nonneg hc (sub_nonneg.mpr (le_of_not_ge hr))])

theorem monopoleLogModel_le_model (r : ℝ) :
    monopoleLogModel r ≤ model r := by
  have hpos := smoothLogRadius_pos r
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hc : 0 ≤ cutoff r := by
    unfold cutoff
    exact Real.smoothTransition.nonneg _
  unfold monopoleLogModel smoothLogRadius at hlog
  unfold model
  calc
    Real.log (1 + cutoff r * (r - 1)) ≤
        (1 + cutoff r * (r - 1)) - 1 := hlog
    _ = cutoff r * (r - 1) := by ring
    _ ≤ cutoff r * r := by
      exact mul_le_mul_of_nonneg_left (by linarith) hc

theorem monopoleLogModel_abs_le_model (r : ℝ) :
    |monopoleLogModel r| ≤ model r := by
  rw [abs_of_nonneg (monopoleLogModel_nonneg r)]
  exact monopoleLogModel_le_model r

theorem monopoleLogModel_deriv_eq_inv_of_two_lt
    (r : ℝ) (hr : 2 < r) :
    deriv monopoleLogModel r = r⁻¹ := by
  have h := Real.hasDerivAt_log (ne_of_gt (lt_trans (by norm_num) hr))
  apply (h.congr_of_eventuallyEq ?_).deriv
  filter_upwards [lt_mem_nhds hr] with x hx
  exact monopoleLogModel_eq_log_of_two_le x hx.le

theorem monopoleLogModel_second_deriv_eq_neg_inv_sq_of_two_lt
    (r : ℝ) (hr : 2 < r) :
    deriv (deriv monopoleLogModel) r = -(r ^ 2)⁻¹ := by
  have h := hasDerivAt_inv (ne_of_gt (lt_trans (by norm_num) hr))
  have h' : HasDerivAt (fun x : ℝ => x⁻¹) (-(r ^ 2)⁻¹) r := by
    simpa only [id_eq] using h
  apply (h'.congr_of_eventuallyEq ?_).deriv
  filter_upwards [lt_mem_nhds hr] with x hx
  exact monopoleLogModel_deriv_eq_inv_of_two_lt x hx

theorem monopoleLogModel_zero : monopoleLogModel 0 = 0 := by
  exact monopoleLogModel_zero_of_le_one 0 (by norm_num)

theorem monopoleLogModel_deriv_zero : deriv monopoleLogModel 0 = 0 := by
  have h : HasDerivAt monopoleLogModel 0 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact monopoleLogModel_zero_of_le_one x hx.le
  exact h.deriv

theorem hartreeScaleLogDensity_measurable :
    Measurable (Function.uncurry (fun r rho =>
      resonancePlus r * hartreeKernel r rho * monopoleLogModel rho)) := by
  exact ((resonancePlus_measurable.comp measurable_fst).mul
    hartreeKernel_uncurry_measurable).mul
      (monopoleLogModel_contDiff_infty.continuous.measurable.comp measurable_snd)

theorem hartree_scale_log_product_integrable :
    Integrable
      (Function.uncurry (fun r rho =>
        resonancePlus r * hartreeKernel r rho * monopoleLogModel rho))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict]
  have hmajor := hartree_scale_affine_product_integrable
  rw [Measure.prod_restrict] at hmajor
  refine hmajor.norm.mono'
    hartreeScaleLogDensity_measurable.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  change
    |resonancePlus p.1 * hartreeKernel p.1 p.2 * monopoleLogModel p.2| ≤
      |resonancePlus p.1 * hartreeKernel p.1 p.2 * model p.2|
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  have hlog := monopoleLogModel_abs_le_model p.2
  have hmodel : 0 ≤ model p.2 := by
    unfold model
    exact mul_nonneg
      (by unfold cutoff; exact Real.smoothTransition.nonneg _)
      hp.2.le
  rw [abs_of_nonneg hmodel]
  exact mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem resonancePlus_nonlocal_log_integrableOn :
    IntegrableOn (fun r : ℝ =>
      resonancePlus r * nonlocalApply monopoleLogModel r) (Ioi 0) := by
  have h := hartree_scale_log_product_integrable.integral_prod_left
  change Integrable (fun r : ℝ =>
    resonancePlus r * nonlocalApply monopoleLogModel r)
    (volume.restrict (Ioi 0))
  refine h.congr ?_
  filter_upwards with r
  unfold nonlocalApply
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with rho
  change resonancePlus r * hartreeKernel r rho * monopoleLogModel rho =
    resonancePlus r * (hartreeKernel r rho * monopoleLogModel rho)
  ring

theorem log_nonlocal_resonancePlus_integrableOn :
    IntegrableOn (fun r : ℝ =>
      monopoleLogModel r * nonlocalApply resonancePlus r) (Ioi 0) := by
  have h := hartree_scale_log_product_integrable.integral_prod_right
  change Integrable (fun r : ℝ =>
    monopoleLogModel r * nonlocalApply resonancePlus r)
    (volume.restrict (Ioi 0))
  refine h.congr ?_
  filter_upwards with rho
  unfold nonlocalApply
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  change resonancePlus r * hartreeKernel r rho * monopoleLogModel rho =
    monopoleLogModel rho * (hartreeKernel rho r * resonancePlus r)
  rw [hartreeKernel_symm r rho]
  ring

theorem hartree_scale_log_pairing :
    (∫ r in Ioi (0 : ℝ),
      resonancePlus r * nonlocalApply monopoleLogModel r) =
      ∫ r in Ioi (0 : ℝ),
        monopoleLogModel r * nonlocalApply resonancePlus r :=
  hartree_nonlocal_pairing_of_integrable resonancePlus monopoleLogModel
    hartree_scale_log_product_integrable

/-- Local differential part of the logarithmic charge density. -/
def hPlusLocalLogDensity (r : ℝ) : ℝ :=
  resonancePlus r * hPlusLocalApply monopoleLogModel r

theorem hPlusLocalLogDensity_continuous :
    Continuous hPlusLocalLogDensity := by
  have hq : ContDiff ℝ ∞ monopoleLogModel :=
    monopoleLogModel_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv monopoleLogModel)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold hPlusLocalLogDensity hPlusLocalApply
  exact resonancePlus_contDiff_infty.continuous.mul
    (hq2.continuous.neg.sub
      ((continuous_const.mul potential_continuous).mul hq.continuous))

theorem hPlusLocalLogDensity_far (r : ℝ) (hr : 2 < r) :
    hPlusLocalLogDensity r =
      resonancePlus r *
        ((r ^ 2)⁻¹ - 3 * potential r * Real.log r) := by
  unfold hPlusLocalLogDensity hPlusLocalApply
  rw [monopoleLogModel_second_deriv_eq_neg_inv_sq_of_two_lt r hr,
    monopoleLogModel_eq_log_of_two_le r hr.le]
  ring

theorem hPlusLocalLogDensity_norm_far_le (r : ℝ) (hr : 2 < r) :
    ‖hPlusLocalLogDensity r‖ ≤
      6 * (1 + r ^ 2)⁻¹ := by
  rw [hPlusLocalLogDensity_far r hr, Real.norm_eq_abs, abs_mul]
  have hrpos : 0 < r := lt_trans (by norm_num) hr
  have hpsi := resonancePlus_abs_le_half r hrpos.le
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos hrpos
  have hinv : (r ^ 2)⁻¹ ≤ 2 * (1 + r ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    rw [show 2 * (1 / (1 + r ^ 2)) = 2 / (1 + r ^ 2) by ring]
    rw [div_le_div_iff₀ hrsq hden]
    nlinarith [sq_nonneg r]
  have hlog0 : 0 ≤ Real.log r :=
    Real.log_nonneg (by linarith)
  have hlogle : Real.log r ≤ 1 + r ^ 2 := by
    exact (Real.log_le_self hrpos.le).trans (by nlinarith [sq_nonneg r])
  have hpot0 : 0 ≤ 3 * potential r * Real.log r :=
    mul_nonneg (mul_nonneg (by norm_num)
      (by unfold potential; positivity)) hlog0
  have hpot : 3 * potential r * Real.log r ≤
      9 * (1 + r ^ 2)⁻¹ := by
    unfold potential
    calc
      3 * (3 / (1 + r ^ 2) ^ 2) * Real.log r =
          9 * Real.log r / (1 + r ^ 2) ^ 2 := by ring
      _ ≤ 9 * (1 + r ^ 2) / (1 + r ^ 2) ^ 2 := by
        gcongr
      _ = 9 * (1 + r ^ 2)⁻¹ := by field_simp
  have habs : |(r ^ 2)⁻¹ - 3 * potential r * Real.log r| ≤
      (r ^ 2)⁻¹ + 3 * potential r * Real.log r := by
    have ha : |(r ^ 2)⁻¹| = (r ^ 2)⁻¹ :=
      abs_of_pos (inv_pos.mpr hrsq)
    have hb : |-(3 * potential r * Real.log r)| =
        3 * potential r * Real.log r := by
      rw [abs_neg, abs_of_nonneg hpot0]
    calc
      |(r ^ 2)⁻¹ - 3 * potential r * Real.log r| =
          |(r ^ 2)⁻¹ + -(3 * potential r * Real.log r)| := by
        rw [sub_eq_add_neg]
      _ ≤ |(r ^ 2)⁻¹| + |-(3 * potential r * Real.log r)| :=
        abs_add_le _ _
      _ = (r ^ 2)⁻¹ + 3 * potential r * Real.log r := by
        rw [ha, hb]
  calc
    |resonancePlus r| *
        |(r ^ 2)⁻¹ - 3 * potential r * Real.log r| ≤
        (1 / 2 : ℝ) *
          ((r ^ 2)⁻¹ + 3 * potential r * Real.log r) :=
      mul_le_mul hpsi habs
        (abs_nonneg _)
        (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (2 * (1 + r ^ 2)⁻¹ + 9 * (1 + r ^ 2)⁻¹) := by
      gcongr
    _ ≤ 6 * (1 + r ^ 2)⁻¹ := by
      have hi : 0 ≤ (1 + r ^ 2)⁻¹ := inv_nonneg.mpr hden.le
      nlinarith

theorem hPlusLocalLogDensity_integrableOn :
    IntegrableOn hPlusLocalLogDensity (Ioi (0 : ℝ)) := by
  have hcompact : IntegrableOn hPlusLocalLogDensity (Ioc (0 : ℝ) 2) :=
    (hPlusLocalLogDensity_continuous.continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun r : ℝ => 6 * (1 + r ^ 2)⁻¹) (Ioi 2) :=
    (integrable_inv_one_add_sq.const_mul 6).integrableOn
  have htail : IntegrableOn hPlusLocalLogDensity (Ioi 2) := by
    refine hmajor.mono'
      hPlusLocalLogDensity_continuous.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hPlusLocalLogDensity_norm_far_le r hr
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
  exact hcompact.union htail

/-- Differential commutator used before the nonlocal Fubini cancellation. -/
def hPlusLocalLogCommutator (r : ℝ) : ℝ :=
  resonancePlus r * hPlusLocalApply monopoleLogModel r -
    hPlusLocalApply resonancePlus r * monopoleLogModel r

theorem hPlusLocalLogCommutator_continuous :
    Continuous hPlusLocalLogCommutator := by
  have hpsi : ContDiff ℝ ∞ resonancePlus := resonancePlus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonancePlus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hpsi2 : ContDiff ℝ ∞ (deriv (deriv resonancePlus)) :=
    (contDiff_infty_iff_deriv.mp hpsi1).2
  have hq : ContDiff ℝ ∞ monopoleLogModel :=
    monopoleLogModel_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv monopoleLogModel)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold hPlusLocalLogCommutator hPlusLocalApply
  exact (hpsi.continuous.mul
    (hq2.continuous.neg.sub
      ((continuous_const.mul potential_continuous).mul hq.continuous))).sub
    ((hpsi2.continuous.neg.sub
      ((continuous_const.mul potential_continuous).mul hpsi.continuous)).mul
      hq.continuous)

theorem hPlusLocalLogCommutator_integrableOn :
    IntegrableOn hPlusLocalLogCommutator (Ioi 0) := by
  have hbase := hPlusLocalLogDensity_integrableOn.sub
    log_nonlocal_resonancePlus_integrableOn
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro r hr
  have hz := hPlus_resonancePlus_zero r hr
  rw [hPlusApply_eq_local_sub_nonlocal] at hz
  have hlocal : hPlusLocalApply resonancePlus r =
      nonlocalApply resonancePlus r := by linarith
  simp only [Pi.sub_apply]
  unfold hPlusLocalLogCommutator hPlusLocalLogDensity
  rw [hlocal]
  ring

theorem greenBoundary_log_at_zero :
    greenBoundary resonancePlus (deriv resonancePlus)
      monopoleLogModel (deriv monopoleLogModel) 0 = 0 := by
  simp [greenBoundary, monopoleLogModel_zero]

theorem hPlus_log_local_commutator_finite (R : ℝ) :
    (∫ r in (0 : ℝ)..R, hPlusLocalLogCommutator r) =
      greenBoundary resonancePlus (deriv resonancePlus)
        monopoleLogModel (deriv monopoleLogModel) R := by
  have hpsi : ContDiff ℝ ∞ resonancePlus := resonancePlus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonancePlus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hq : ContDiff ℝ ∞ monopoleLogModel :=
    monopoleLogModel_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hpsiD (r : ℝ) :
      HasDerivAt resonancePlus (deriv resonancePlus r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi).1 r).hasDerivAt
  have hpsiDD (r : ℝ) :
      HasDerivAt (deriv resonancePlus)
        (deriv (deriv resonancePlus) r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi1).1 r).hasDerivAt
  have hqD (r : ℝ) :
      HasDerivAt monopoleLogModel (deriv monopoleLogModel r) r :=
    ((contDiff_infty_iff_deriv.mp hq).1 r).hasDerivAt
  have hqDD (r : ℝ) :
      HasDerivAt (deriv monopoleLogModel)
        (deriv (deriv monopoleLogModel) r) r :=
    ((contDiff_infty_iff_deriv.mp hq1).1 r).hasDerivAt
  let V : ℝ → ℝ := fun r => 3 * potential r
  let f : ℝ → ℝ := fun r =>
    resonancePlus r *
        ((-deriv (deriv monopoleLogModel) r) -
          V r * monopoleLogModel r) -
      (((-deriv (deriv resonancePlus) r) -
        V r * resonancePlus r) * monopoleLogModel r)
  have hrewrite : f = hPlusLocalLogCommutator := by
    funext r
    unfold f V hPlusLocalLogCommutator hPlusLocalApply
    ring
  have hint : IntervalIntegrable f volume 0 R := by
    rw [hrewrite]
    exact hPlusLocalLogCommutator_continuous.intervalIntegrable 0 R
  have hmain := green_localSchrodinger (0 : ℝ) R V
    resonancePlus (deriv resonancePlus) (deriv (deriv resonancePlus))
    monopoleLogModel (deriv monopoleLogModel)
    (deriv (deriv monopoleLogModel))
    hpsiD hpsiDD hqD hqDD hint
  change (∫ r in (0 : ℝ)..R, f r) = _ at hmain
  rw [hrewrite] at hmain
  simpa only [greenBoundary_log_at_zero, sub_zero] using hmain

theorem log_div_self_tendsto_zero :
    Tendsto (fun r : ℝ => Real.log r / r) atTop (𝓝 (0 : ℝ)) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
    (by norm_num : (1 : ℝ) ≠ 0)

theorem greenBoundary_log_tendsto_zero :
    Tendsto
      (fun R : ℝ => greenBoundary resonancePlus (deriv resonancePlus)
        monopoleLogModel (deriv monopoleLogModel) R)
      atTop (𝓝 (0 : ℝ)) := by
  have hfirst : Tendsto (fun R : ℝ =>
      -resonancePlus R * R⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have h := resonancePlus_tendsto_neg_half.neg.mul tendsto_inv_atTop_zero
    simpa using h
  have hsecond : Tendsto (fun R : ℝ =>
      deriv resonancePlus R * Real.log R) atTop (𝓝 (0 : ℝ)) := by
    have h := radius_resonancePlus_deriv_tendsto_zero.mul
      log_div_self_tendsto_zero
    have h0 : Tendsto
        (fun R : ℝ => (R * deriv resonancePlus R) *
          (Real.log R / R)) atTop (𝓝 (0 : ℝ)) := by
      simpa using h
    apply h0.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with R hR
    have hne : R ≠ 0 := by linarith
    field_simp [hne]
  have hsum := hfirst.add hsecond
  have hzero : Tendsto
      (fun R : ℝ => -resonancePlus R * R⁻¹ +
        deriv resonancePlus R * Real.log R)
      atTop (𝓝 (0 : ℝ)) := by simpa using hsum
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with R hR
  unfold greenBoundary
  rw [monopoleLogModel_deriv_eq_inv_of_two_lt R hR,
    monopoleLogModel_eq_log_of_two_le R hR.le]

theorem hPlus_log_local_commutator_integral_eq_zero :
    (∫ r in Ioi (0 : ℝ), hPlusLocalLogCommutator r) = 0 := by
  have hIntegral := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    hPlusLocalLogCommutator_integrableOn tendsto_id
  have hBoundary : Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R, hPlusLocalLogCommutator r)
      atTop (𝓝 (0 : ℝ)) :=
    greenBoundary_log_tendsto_zero.congr'
      (Filter.Eventually.of_forall fun R : ℝ =>
        (hPlus_log_local_commutator_finite R).symm)
  exact tendsto_nhds_unique hIntegral hBoundary

/-- Full logarithmic charge density. -/
def hPlusLogDensity (r : ℝ) : ℝ :=
  resonancePlus r * hPlusApply monopoleLogModel r

theorem hPlusLogDensity_eq_local_sub_nonlocal (r : ℝ) :
    hPlusLogDensity r =
      hPlusLocalLogDensity r -
        resonancePlus r * nonlocalApply monopoleLogModel r := by
  unfold hPlusLogDensity hPlusLocalLogDensity
  rw [hPlusApply_eq_local_sub_nonlocal]
  ring

theorem hPlusLogDensity_integrableOn :
    IntegrableOn hPlusLogDensity (Ioi 0) := by
  have h := hPlusLocalLogDensity_integrableOn.sub
    resonancePlus_nonlocal_log_integrableOn
  refine h.congr_fun ?_ measurableSet_Ioi
  intro r _
  simp only [Pi.sub_apply]
  exact (hPlusLogDensity_eq_local_sub_nonlocal r).symm

/-- The logarithmic subtraction has exactly zero affine threshold charge. -/
theorem monopole_log_model_charge_eq_zero :
    (∫ r in Ioi (0 : ℝ),
      resonancePlus r * hPlusApply monopoleLogModel r) = 0 := by
  have hcomm := hPlus_log_local_commutator_integral_eq_zero
  have hcommEq :
      (∫ r in Ioi (0 : ℝ), hPlusLocalLogCommutator r) =
        ∫ r in Ioi (0 : ℝ),
          hPlusLocalLogDensity r -
            monopoleLogModel r * nonlocalApply resonancePlus r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hz := hPlus_resonancePlus_zero r hr
    rw [hPlusApply_eq_local_sub_nonlocal] at hz
    have hlocal : hPlusLocalApply resonancePlus r =
        nonlocalApply resonancePlus r := by linarith
    unfold hPlusLocalLogCommutator hPlusLocalLogDensity
    rw [hlocal]
    ring
  rw [hcommEq, integral_sub hPlusLocalLogDensity_integrableOn
    log_nonlocal_resonancePlus_integrableOn] at hcomm
  have hpair := hartree_scale_log_pairing
  have hdensity : hPlusLogDensity = fun r : ℝ =>
      hPlusLocalLogDensity r -
        resonancePlus r * nonlocalApply monopoleLogModel r := by
    funext r
    exact hPlusLogDensity_eq_local_sub_nonlocal r
  change (∫ r in Ioi (0 : ℝ), hPlusLogDensity r) = 0
  rw [hdensity, integral_sub hPlusLocalLogDensity_integrableOn
    resonancePlus_nonlocal_log_integrableOn]
  linarith

end HBL.Modulation.AffineTail
