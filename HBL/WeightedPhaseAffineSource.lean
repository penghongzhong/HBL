import HBL.AffineTailLemmaClosed
import HBL.WeightedPhaseSourceFredholmBridge
import Mathlib.Tactic

/-!
# Phase-channel affine source in the manuscript weighted L2 class

For the concrete H_minus operator and the fixed affine cutoff model,
this file proves the missing source-space mapping statement

  H_minus (chi_aff r) ∈ L^{2,sigma}(0,∞),    sigma ≤ 2.

The compact part follows from actual smoothness; beyond r=2 the source is
-3r/(1+r²)^2.  Consequently any affine-charge corrected source remains
in the same weighted space.  No right inverse or source regularity is
inserted as an external assumption.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace HBL.Modulation.AffineTail

theorem phaseAffineSource_continuous :
    Continuous (channelAffineSource HartreeChannel.minus) := by
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  change Continuous (fun r : ℝ =>
    -deriv (deriv model) r - potential r * model r)
  exact hq2.continuous.neg.sub
    (potential_continuous.mul hq.continuous)

theorem affineJapaneseWeight_continuous (sigma : ℝ) :
    Continuous (affineJapaneseWeight sigma) := by
  unfold affineJapaneseWeight
  have hb : Continuous (fun r : ℝ => 1 + r ^ 2) := by fun_prop
  exact hb.rpow_const (fun r => Or.inl (by positivity))

theorem phaseAffineSource_far
    (r : ℝ) (hr : 2 < r) :
    channelAffineSource HartreeChannel.minus r =
      -(3 * r * (1 + r ^ 2)⁻¹ ^ 2) := by
  change -deriv (deriv model) r - potential r * model r = _
  rw [model_second_deriv_eq_zero_of_two_lt r hr,
    model_eq_id_of_two_le r hr.le]
  simp only [neg_zero, zero_sub]
  unfold potential
  rw [div_eq_mul_inv, inv_pow]
  ring

theorem affineJapaneseWeight_le_one_add_sq
    (sigma r : ℝ) (hsigma : sigma ≤ 2) :
    affineJapaneseWeight sigma r ≤ 1 + r ^ 2 := by
  unfold affineJapaneseWeight
  have hbase : (1 : ℝ) ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg r]
  have hs : sigma / 2 ≤ 1 := by linarith
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hbase hs)

theorem phaseAffineSource_weighted_sq_far
    (sigma r : ℝ) (hsigma : sigma ≤ 2) (hr : 2 < r) :
    (affineJapaneseWeight sigma r *
      channelAffineSource HartreeChannel.minus r) ^ 2 ≤
      9 * (1 + r ^ 2)⁻¹ := by
  have hr0 : 0 ≤ r := by linarith
  have hden : 1 + r ^ 2 ≠ 0 := by positivity
  have hw0 : 0 ≤ affineJapaneseWeight sigma r := by
    unfold affineJapaneseWeight
    positivity
  have hw : affineJapaneseWeight sigma r ≤ 1 + r ^ 2 :=
    affineJapaneseWeight_le_one_add_sq sigma r hsigma
  have hsourceAbs :
      |channelAffineSource HartreeChannel.minus r| =
        3 * r * (1 + r ^ 2)⁻¹ ^ 2 := by
    rw [phaseAffineSource_far r hr, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤
        3 * r * (1 + r ^ 2)⁻¹ ^ 2)]
  have habs :
      |affineJapaneseWeight sigma r *
        channelAffineSource HartreeChannel.minus r| ≤
        3 * r * (1 + r ^ 2)⁻¹ := by
    rw [abs_mul, abs_of_nonneg hw0, hsourceAbs]
    calc
      affineJapaneseWeight sigma r *
          (3 * r * (1 + r ^ 2)⁻¹ ^ 2) ≤
          (1 + r ^ 2) * (3 * r * (1 + r ^ 2)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
      _ = 3 * r * (1 + r ^ 2)⁻¹ := by
        field_simp [hden]
  have hsq :
      (affineJapaneseWeight sigma r *
        channelAffineSource HartreeChannel.minus r) ^ 2 ≤
        (3 * r * (1 + r ^ 2)⁻¹) ^ 2 := by
    have h := mul_self_le_mul_self
      (abs_nonneg (affineJapaneseWeight sigma r *
        channelAffineSource HartreeChannel.minus r)) habs
    have hsqabs :
        |affineJapaneseWeight sigma r *
          channelAffineSource HartreeChannel.minus r| ^ 2 ≤
        (3 * r * (1 + r ^ 2)⁻¹) ^ 2 := by
      simpa only [pow_two] using h
    simpa only [sq_abs] using hsqabs
  calc
    (affineJapaneseWeight sigma r *
        channelAffineSource HartreeChannel.minus r) ^ 2 ≤
        (3 * r * (1 + r ^ 2)⁻¹) ^ 2 := hsq
    _ = 9 * r ^ 2 * (1 + r ^ 2)⁻¹ ^ 2 := by ring
    _ ≤ 9 * (1 + r ^ 2) * (1 + r ^ 2)⁻¹ ^ 2 := by
      apply mul_le_mul_of_nonneg_right (show
        9 * r ^ 2 ≤ 9 * (1 + r ^ 2) by nlinarith) (by positivity)
    _ = 9 * (1 + r ^ 2)⁻¹ := by
      field_simp [hden]

theorem phaseAffineSource_inWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2) :
    InWeightedL2 sigma (channelAffineSource HartreeChannel.minus) := by
  have hc : Continuous (fun r : ℝ =>
      affineJapaneseWeight sigma r *
        channelAffineSource HartreeChannel.minus r) :=
    (affineJapaneseWeight_continuous sigma).mul
      phaseAffineSource_continuous
  have hcompact : IntegrableOn
      (fun r : ℝ =>
        (affineJapaneseWeight sigma r *
          channelAffineSource HartreeChannel.minus r) ^ 2)
      (Ioc (0 : ℝ) 2) :=
    (hc.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun r : ℝ => 9 * (1 + r ^ 2)⁻¹) (Ioi 2) :=
    (integrable_inv_one_add_sq.const_mul 9).integrableOn
  have htail : IntegrableOn
      (fun r : ℝ =>
        (affineJapaneseWeight sigma r *
          channelAffineSource HartreeChannel.minus r) ^ 2) (Ioi 2) := by
    refine hmajor.mono'
      (hc.pow 2).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact phaseAffineSource_weighted_sq_far sigma r hsigma hr
  have hall : IntegrableOn
      (fun r : ℝ =>
        (affineJapaneseWeight sigma r *
          channelAffineSource HartreeChannel.minus r) ^ 2) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
    exact hcompact.union htail
  unfold InWeightedL2
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable.restrict).2
  exact hall

theorem phaseAffine_correctedSource_inWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (alpha : ℝ) :
    InWeightedL2 sigma (fun r =>
      F r - alpha * channelAffineSource HartreeChannel.minus r) := by
  have hmodel := phaseAffineSource_inWeightedL2 sigma hsigma
  unfold InWeightedL2 at hF hmodel ⊢
  have h := hF.sub (hmodel.const_mul alpha)
  convert h using 1
  funext r
  simp only [Pi.sub_apply]
  ring

#print axioms phaseAffineSource_weighted_sq_far
#print axioms phaseAffineSource_inWeightedL2
#print axioms phaseAffine_correctedSource_inWeightedL2

end HBL.Modulation.AffineTail
