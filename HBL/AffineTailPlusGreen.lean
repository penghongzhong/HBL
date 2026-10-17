import HBL.AffineTailHartreeIntegrability
import HBL.AffineTailPlusBoundaryLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The corrected full-half-line Green identity in the real Hartree channel.
The local Wronskian term is integrated exactly and the nonlocal commutator
is cancelled only after the absolute product-integrability theorem permits
Fubini.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- Differential part of the real-channel half-line operator. -/
def hPlusLocalApply (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  -deriv (deriv q) r - 3 * potential r * q r

theorem hPlusApply_eq_local_sub_nonlocal (q : ℝ → ℝ) (r : ℝ) :
    hPlusApply q r = hPlusLocalApply q r - nonlocalApply q r := by
  rfl

theorem resonancePlus_contDiff_infty :
    ContDiff ℝ ∞ resonancePlus := by
  change ContDiff ℝ ∞ radialResonancePlus
  exact radialResonancePlus_contDiff_infty

theorem potential_continuous : Continuous potential := by
  unfold potential
  fun_prop (discharger := intro; positivity)

theorem model_second_deriv_eq_zero_of_two_lt
    (r : ℝ) (hr : 2 < r) :
    deriv (deriv model) r = 0 := by
  have h : HasDerivAt (deriv model) 0 r := by
    apply (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hr] with x hx
    exact model_deriv_eq_one_of_two_lt x hx
  exact h.deriv

theorem resonancePlus_abs_le_half (r : ℝ) (hr : 0 ≤ r) :
    |resonancePlus r| ≤ 1 / 2 := by
  rw [resonancePlus_def, dilationGenerator_bubble_closed, abs_mul,
    abs_of_nonneg hr, abs_div,
    abs_of_pos (by positivity : 0 < 2 * Real.sqrt (1 + r ^ 2) ^ 3)]
  have hspos : 0 < Real.sqrt (1 + r ^ 2) := by positivity
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hrle : r ≤ Real.sqrt (1 + r ^ 2) := by
    rw [Real.le_sqrt hr (by positivity)]
    nlinarith [sq_nonneg r]
  have hdiff : |1 - r ^ 2| ≤ 1 + r ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg r]
  have hnum : r * |1 - r ^ 2| ≤
      Real.sqrt (1 + r ^ 2) ^ 3 := by
    calc
      r * |1 - r ^ 2| ≤
          Real.sqrt (1 + r ^ 2) * (1 + r ^ 2) :=
        mul_le_mul hrle hdiff (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (1 + r ^ 2) *
          (Real.sqrt (1 + r ^ 2) ^ 2) := by
        exact congrArg (fun x : ℝ => Real.sqrt (1 + r ^ 2) * x) hs2.symm
      _ = Real.sqrt (1 + r ^ 2) ^ 3 := by ring
  rw [show r * (|1 - r ^ 2| /
      (2 * Real.sqrt (1 + r ^ 2) ^ 3)) =
    (r * |1 - r ^ 2|) /
      (2 * Real.sqrt (1 + r ^ 2) ^ 3) by ring]
  rw [div_le_iff₀ (by positivity :
    0 < 2 * Real.sqrt (1 + r ^ 2) ^ 3)]
  nlinarith

/-- Local part of the affine charge density. -/
def hPlusLocalAffineDensity (r : ℝ) : ℝ :=
  resonancePlus r * hPlusLocalApply model r

theorem hPlusLocalAffineDensity_continuous :
    Continuous hPlusLocalAffineDensity := by
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold hPlusLocalAffineDensity hPlusLocalApply
  exact resonancePlus_contDiff_infty.continuous.mul
    (hq2.continuous.neg.sub
      ((continuous_const.mul potential_continuous).mul hq.continuous))

theorem hPlusLocalAffineDensity_far (r : ℝ) (hr : 2 < r) :
    hPlusLocalAffineDensity r =
      -3 * resonancePlus r * potential r * r := by
  unfold hPlusLocalAffineDensity hPlusLocalApply
  rw [model_second_deriv_eq_zero_of_two_lt r hr,
    model_eq_id_of_two_le r hr.le]
  ring

theorem hPlusLocalAffineDensity_norm_far_le
    (r : ℝ) (hr : 2 < r) :
    ‖hPlusLocalAffineDensity r‖ ≤
      (9 / 2 : ℝ) * (1 + r ^ 2)⁻¹ := by
  rw [hPlusLocalAffineDensity_far r hr, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ r from hr.le.trans' (by norm_num)),
    abs_of_nonneg (show 0 ≤ potential r by unfold potential; positivity)]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hpsi := resonancePlus_abs_le_half r (by linarith)
  have hrle : r ≤ 1 + r ^ 2 := by
    nlinarith [sq_nonneg (r - 1)]
  unfold potential
  have hden : 0 < 1 + r ^ 2 := by positivity
  rw [div_eq_mul_inv]
  have htail : r * ((1 + r ^ 2) ^ 2)⁻¹ ≤ (1 + r ^ 2)⁻¹ := by
    rw [← inv_pow]
    calc
      r * ((1 + r ^ 2)⁻¹) ^ 2 ≤
          (1 + r ^ 2) * ((1 + r ^ 2)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right hrle (sq_nonneg _)
      _ = (1 + r ^ 2)⁻¹ := by field_simp
  have hprod : |resonancePlus r| *
      (r * ((1 + r ^ 2) ^ 2)⁻¹) ≤
      (1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ :=
    mul_le_mul hpsi htail
      (mul_nonneg (by linarith) (inv_nonneg.mpr (sq_nonneg _)))
      (by norm_num)
  calc
    3 * |resonancePlus r| *
        (3 * ((1 + r ^ 2) ^ 2)⁻¹) * r =
        9 * (|resonancePlus r| *
          (r * ((1 + r ^ 2) ^ 2)⁻¹)) := by ring
    _ ≤ 9 * ((1 / 2 : ℝ) * (1 + r ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (9 / 2 : ℝ) * (1 + r ^ 2)⁻¹ := by ring

theorem hPlusLocalAffineDensity_integrableOn :
    IntegrableOn hPlusLocalAffineDensity (Ioi (0 : ℝ)) := by
  have hcompact : IntegrableOn hPlusLocalAffineDensity (Ioc (0 : ℝ) 2) :=
    (hPlusLocalAffineDensity_continuous.continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun r : ℝ => (9 / 2 : ℝ) * (1 + r ^ 2)⁻¹) (Ioi 2) :=
    (integrable_inv_one_add_sq.const_mul (9 / 2 : ℝ)).integrableOn
  have htail : IntegrableOn hPlusLocalAffineDensity (Ioi 2) := by
    refine hmajor.mono'
      hPlusLocalAffineDensity_continuous.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hPlusLocalAffineDensity_norm_far_le r hr
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
  exact hcompact.union htail

theorem resonancePlus_nonlocal_model_integrableOn :
    IntegrableOn (fun r : ℝ =>
      resonancePlus r * nonlocalApply model r) (Ioi 0) := by
  have h := hartree_scale_affine_product_integrable.integral_prod_left
  change Integrable (fun r : ℝ =>
    resonancePlus r * nonlocalApply model r)
    (volume.restrict (Ioi 0))
  refine h.congr ?_
  filter_upwards with r
  unfold nonlocalApply
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with rho
  change resonancePlus r * hartreeKernel r rho * model rho =
    resonancePlus r * (hartreeKernel r rho * model rho)
  ring

theorem model_nonlocal_resonancePlus_integrableOn :
    IntegrableOn (fun r : ℝ =>
      model r * nonlocalApply resonancePlus r) (Ioi 0) := by
  have h := hartree_scale_affine_product_integrable.integral_prod_right
  change Integrable (fun r : ℝ =>
    model r * nonlocalApply resonancePlus r)
    (volume.restrict (Ioi 0))
  refine h.congr ?_
  filter_upwards with rho
  unfold nonlocalApply
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  change resonancePlus r * hartreeKernel r rho * model rho =
    model rho * (hartreeKernel rho r * resonancePlus r)
  rw [hartreeKernel_symm r rho]
  ring

/-- The differential Green commutator before the nonlocal cancellation. -/
def hPlusLocalCommutator (r : ℝ) : ℝ :=
  resonancePlus r * hPlusLocalApply model r -
    hPlusLocalApply resonancePlus r * model r

theorem hPlusLocalCommutator_continuous :
    Continuous hPlusLocalCommutator := by
  have hpsi : ContDiff ℝ ∞ resonancePlus := resonancePlus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonancePlus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hpsi2 : ContDiff ℝ ∞ (deriv (deriv resonancePlus)) :=
    (contDiff_infty_iff_deriv.mp hpsi1).2
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold hPlusLocalCommutator hPlusLocalApply
  exact (hpsi.continuous.mul
    (hq2.continuous.neg.sub
      ((continuous_const.mul potential_continuous).mul hq.continuous))).sub
    ((hpsi2.continuous.neg.sub
      ((continuous_const.mul potential_continuous).mul hpsi.continuous)).mul
      hq.continuous)

theorem hPlusLocalCommutator_integrableOn :
    IntegrableOn hPlusLocalCommutator (Ioi 0) := by
  have hbase := hPlusLocalAffineDensity_integrableOn.sub
    model_nonlocal_resonancePlus_integrableOn
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro r hr
  have hz := hPlus_resonancePlus_zero r hr
  rw [hPlusApply_eq_local_sub_nonlocal] at hz
  have hlocal : hPlusLocalApply resonancePlus r =
      nonlocalApply resonancePlus r := by linarith
  simp only [Pi.sub_apply]
  unfold hPlusLocalCommutator hPlusLocalAffineDensity
  rw [hlocal]
  ring

/-- Exact finite-radius Green formula for the differential commutator. -/
theorem hPlus_local_commutator_finite (R : ℝ) :
    (∫ r in (0 : ℝ)..R, hPlusLocalCommutator r) =
      greenBoundary resonancePlus (deriv resonancePlus)
        model (deriv model) R := by
  have hpsi : ContDiff ℝ ∞ resonancePlus := resonancePlus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonancePlus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hpsiD (r : ℝ) :
      HasDerivAt resonancePlus (deriv resonancePlus r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi).1 r).hasDerivAt
  have hpsiDD (r : ℝ) :
      HasDerivAt (deriv resonancePlus)
        (deriv (deriv resonancePlus) r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi1).1 r).hasDerivAt
  have hqD (r : ℝ) : HasDerivAt model (deriv model r) r :=
    ((contDiff_infty_iff_deriv.mp hq).1 r).hasDerivAt
  have hqDD (r : ℝ) :
      HasDerivAt (deriv model) (deriv (deriv model) r) r :=
    ((contDiff_infty_iff_deriv.mp hq1).1 r).hasDerivAt
  let V : ℝ → ℝ := fun r => 3 * potential r
  let f : ℝ → ℝ := fun r =>
    resonancePlus r *
        ((-deriv (deriv model) r) - V r * model r) -
      (((-deriv (deriv resonancePlus) r) -
        V r * resonancePlus r) * model r)
  have hrewrite : f = hPlusLocalCommutator := by
    funext r
    unfold f V hPlusLocalCommutator hPlusLocalApply
    ring
  have hint : IntervalIntegrable f volume 0 R := by
    rw [hrewrite]
    exact hPlusLocalCommutator_continuous.intervalIntegrable 0 R
  have hmain := green_localSchrodinger (0 : ℝ) R V
    resonancePlus (deriv resonancePlus) (deriv (deriv resonancePlus))
    model (deriv model) (deriv (deriv model))
    hpsiD hpsiDD hqD hqDD hint
  change (∫ r in (0 : ℝ)..R, f r) = _ at hmain
  rw [hrewrite] at hmain
  simpa only [greenBoundary_plus_at_zero, sub_zero] using hmain

/-- The full differential commutator is the far Wronskian value `1/2`. -/
theorem hPlus_local_commutator_integral_eq_half :
    (∫ r in Ioi (0 : ℝ), hPlusLocalCommutator r) = 1 / 2 := by
  have hIntegral := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    hPlusLocalCommutator_integrableOn tendsto_id
  have hBoundary : Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R, hPlusLocalCommutator r)
      atTop (𝓝 (1 / 2 : ℝ)) :=
    greenBoundary_plus_tendsto_half.congr'
      (Filter.Eventually.of_forall fun R : ℝ =>
        (hPlus_local_commutator_finite R).symm)
  exact tendsto_nhds_unique hIntegral hBoundary

/-- Complete real-channel affine charge density. -/
def hPlusAffineDensity (r : ℝ) : ℝ :=
  resonancePlus r * hPlusApply model r

theorem hPlusAffineDensity_eq_local_sub_nonlocal (r : ℝ) :
    hPlusAffineDensity r =
      hPlusLocalAffineDensity r -
        resonancePlus r * nonlocalApply model r := by
  unfold hPlusAffineDensity hPlusLocalAffineDensity
  rw [hPlusApply_eq_local_sub_nonlocal]
  ring

theorem hPlusAffineDensity_integrableOn :
    IntegrableOn hPlusAffineDensity (Ioi 0) := by
  have h := hPlusLocalAffineDensity_integrableOn.sub
    resonancePlus_nonlocal_model_integrableOn
  refine h.congr_fun ?_ measurableSet_Ioi
  intro r _
  simp only [Pi.sub_apply]
  exact (hPlusAffineDensity_eq_local_sub_nonlocal r).symm

/-- The corrected Green identity, including and then cancelling the
nonlocal commutator, gives the real-channel affine charge `-c₊=1/2`. -/
theorem hPlus_affine_pairing_eq_half :
    (∫ r in Ioi (0 : ℝ),
      resonancePlus r * hPlusApply model r) = 1 / 2 := by
  have hcomm := hPlus_local_commutator_integral_eq_half
  have hcommEq :
      (∫ r in Ioi (0 : ℝ), hPlusLocalCommutator r) =
        ∫ r in Ioi (0 : ℝ),
          hPlusLocalAffineDensity r -
            model r * nonlocalApply resonancePlus r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hz := hPlus_resonancePlus_zero r hr
    rw [hPlusApply_eq_local_sub_nonlocal] at hz
    have hlocal : hPlusLocalApply resonancePlus r =
        nonlocalApply resonancePlus r := by linarith
    unfold hPlusLocalCommutator hPlusLocalAffineDensity
    rw [hlocal]
    ring
  rw [hcommEq, integral_sub hPlusLocalAffineDensity_integrableOn
    model_nonlocal_resonancePlus_integrableOn] at hcomm
  have hpair := hartree_scale_affine_pairing
  have hdensity : hPlusAffineDensity = fun r : ℝ =>
      hPlusLocalAffineDensity r -
        resonancePlus r * nonlocalApply model r := by
    funext r
    exact hPlusAffineDensity_eq_local_sub_nonlocal r
  change (∫ r in Ioi (0 : ℝ), hPlusAffineDensity r) = 1 / 2
  rw [hdensity, integral_sub hPlusLocalAffineDensity_integrableOn
    resonancePlus_nonlocal_model_integrableOn]
  linarith

end HBL.Modulation.AffineTail
