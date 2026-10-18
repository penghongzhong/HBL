import HBL.MonopoleFredholmSource
import HBL.L2KernelPointwise
import HBL.WeightedFreeGreenPointwise
import HBL.WeightedHartreeBirmanSchwinger

/-!
The concrete weighted datum for the first monopole Fredholm problem.

The manuscript conjugates a half-line function `q` by
`x = (1+r²)⁻¹ q`.  This file first realizes the logarithmic and affine
models in the weighted `L²` space and then identifies the abstract
Hilbert--Schmidt Hartree action with the conjugated pointwise nonlocal
operator.  The cancellation between `r W³` and `-(log r)''` is kept
explicit; neither term is separately admissible after multiplication by
`1+r²`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The affine cutoff after the endpoint conjugation. -/
def weightedAffineModel (r : ℝ) : ℝ :=
  weightedGreenDecay r * model r

/-- The logarithmic cutoff after the endpoint conjugation. -/
def weightedLogModel (r : ℝ) : ℝ :=
  weightedGreenDecay r * monopoleLogModel r

theorem weightedAffineModel_continuous :
    Continuous weightedAffineModel := by
  unfold weightedAffineModel
  exact weightedGreenDecay_continuous.mul model_contDiff_infty.continuous

theorem weightedLogModel_continuous :
    Continuous weightedLogModel := by
  unfold weightedLogModel
  exact weightedGreenDecay_continuous.mul
    monopoleLogModel_contDiff_infty.continuous

theorem weightedAffineModel_memLp_two :
    MemLp weightedAffineModel 2 halfLineMeasure := by
  refine weightedGreenOutputMajorant_memLp_two.mono'
    weightedAffineModel_continuous.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hc0 : 0 ≤ cutoff r := Real.smoothTransition.nonneg _
  have hc1 : cutoff r ≤ 1 := Real.smoothTransition.le_one _
  rw [Real.norm_eq_abs, weightedAffineModel,
    weightedGreenOutputMajorant, abs_mul,
    abs_of_nonneg (weightedGreenDecay_nonneg r), model]
  have hr0 : 0 ≤ r := hr.le
  rw [abs_mul, abs_of_nonneg hc0, abs_of_nonneg hr0]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left hr0 hc1) (weightedGreenDecay_nonneg r))

theorem weightedLogModel_memLp_two :
    MemLp weightedLogModel 2 halfLineMeasure := by
  refine weightedAffineModel_memLp_two.mono'
    weightedLogModel_continuous.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, weightedLogModel, weightedAffineModel,
    abs_mul,
    abs_of_nonneg (weightedGreenDecay_nonneg r)]
  exact mul_le_mul_of_nonneg_left
    (monopoleLogModel_abs_le_model r) (weightedGreenDecay_nonneg r)

/-- The weighted affine model as an actual half-line `L²` vector. -/
def weightedAffineModelL2 : RealL2 halfLineMeasure :=
  weightedAffineModel_memLp_two.toLp weightedAffineModel

/-- The weighted logarithmic model as an actual half-line `L²` vector. -/
def weightedLogModelL2 : RealL2 halfLineMeasure :=
  weightedLogModel_memLp_two.toLp weightedLogModel

theorem weightedAffineModelL2_ae :
    (weightedAffineModelL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedAffineModel :=
  weightedAffineModel_memLp_two.coeFn_toLp

theorem weightedLogModelL2_ae :
    (weightedLogModelL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedLogModel :=
  weightedLogModel_memLp_two.coeFn_toLp

/-- Conjugating a pointwise Hartree input agrees almost everywhere with
the abstract weighted Hartree operator. -/
theorem weightedHartreeOperator_conjugation
    (q : ℝ → ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2
      halfLineMeasure) :
    (weightedHartreeOperator
        (hq.toLp (fun r => weightedGreenDecay r * q r)) : ℝ → ℝ)
      =ᵐ[halfLineMeasure]
        fun r => (1 + r ^ 2) * nonlocalApply q r := by
  have hop := operator_toLp_ae_eq_integral
    weightedHartreeKernel weightedHartreeKernel_memLp_two
      (hq.toLp (fun r => weightedGreenDecay r * q r))
  have hop' :
      (weightedHartreeOperator
          (hq.toLp (fun r => weightedGreenDecay r * q r)) : ℝ → ℝ)
        =ᵐ[halfLineMeasure]
          fun x => ∫ y, weightedHartreeKernel x y *
            (hq.toLp (fun r => weightedGreenDecay r * q r)) y
              ∂halfLineMeasure := by
    simpa [weightedHartreeOperator, weightedHartreeKernelL2] using hop
  have hqae := hq.coeFn_toLp
  filter_upwards [hop'] with r hr
  rw [hr]
  unfold nonlocalApply
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hqae] with rho hρ
  rw [hρ]
  unfold weightedHartreeKernel hartreeKernel hartreeRadialLog
    weightedGreenDecay bubble
  have hsr : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hsρ : Real.sqrt (1 + rho ^ 2) ≠ 0 := by positivity
  have hsr2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hsρ2 : Real.sqrt (1 + rho ^ 2) ^ 2 = 1 + rho ^ 2 :=
    Real.sq_sqrt (by positivity)
  field_simp [hsr, hsρ]
  rw [hsr2, hsρ2]

theorem weightedHartreeOperator_affine_ae :
    (weightedHartreeOperator weightedAffineModelL2 : ℝ → ℝ)
      =ᵐ[halfLineMeasure]
        fun r => (1 + r ^ 2) * nonlocalApply model r := by
  exact weightedHartreeOperator_conjugation model
    weightedAffineModel_memLp_two

theorem weightedHartreeOperator_log_ae :
    (weightedHartreeOperator weightedLogModelL2 : ℝ → ℝ)
      =ᵐ[halfLineMeasure]
        fun r => (1 + r ^ 2) * nonlocalApply monopoleLogModel r := by
  exact weightedHartreeOperator_conjugation monopoleLogModel
    weightedLogModel_memLp_two

/-- The only non-`L²` pieces of the weighted logarithmic source, grouped
so that their leading constants cancel. -/
def weightedMonopoleCancellation (r : ℝ) : ℝ :=
  (1 + r ^ 2) *
    (r * bubble r ^ 3 + deriv (deriv monopoleLogModel) r)

theorem weightedMonopoleCancellation_continuous :
    Continuous weightedMonopoleCancellation := by
  have hq : ContDiff ℝ ∞ monopoleLogModel :=
    monopoleLogModel_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv monopoleLogModel)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold weightedMonopoleCancellation
  exact (continuous_const.add (continuous_id.pow 2)).mul
    ((continuous_id.mul (bubble_contDiff_infty.continuous.pow 3)).add
      hq2.continuous)

theorem weightedMonopoleCancellation_far
    (r : ℝ) (hr : 2 < r) :
    weightedMonopoleCancellation r =
      r / Real.sqrt (1 + r ^ 2) - (1 + r ^ 2) / r ^ 2 := by
  rw [weightedMonopoleCancellation,
    monopoleLogModel_second_deriv_eq_neg_inv_sq_of_two_lt r hr]
  unfold bubble
  have hs : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hterm :
      (1 + r ^ 2) *
          (r * (Real.sqrt (1 + r ^ 2))⁻¹ ^ 3) =
        r / Real.sqrt (1 + r ^ 2) := by
    calc
      (1 + r ^ 2) *
          (r * (Real.sqrt (1 + r ^ 2))⁻¹ ^ 3) =
          Real.sqrt (1 + r ^ 2) ^ 2 *
            (r * (Real.sqrt (1 + r ^ 2))⁻¹ ^ 3) := by rw [hs2]
      _ = r / Real.sqrt (1 + r ^ 2) := by field_simp [hs]
  rw [mul_add, hterm]
  field_simp [hr0]
  ring

theorem weightedMonopoleCancellation_norm_far_le
    (r : ℝ) (hr : 2 < r) :
    ‖weightedMonopoleCancellation r‖ ≤
      2 * weightedGreenDecay r := by
  rw [weightedMonopoleCancellation_far r hr, Real.norm_eq_abs]
  have hr0 : 0 < r := by linarith
  let s := Real.sqrt (1 + r ^ 2)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 1 + r ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  have hrs : r ≤ s := by
    dsimp [s]
    rw [Real.le_sqrt hr0.le (by positivity)]
    linarith
  have hsum : 2 * r ≤ s + r := by linarith
  have hprod : 2 * r ^ 2 ≤ s * (s + r) := by
    calc
      2 * r ^ 2 = r * (2 * r) := by ring
      _ ≤ s * (s + r) :=
        mul_le_mul hrs hsum (by positivity) (by positivity)
  have hid : 1 - r / s = 1 / (s * (s + r)) := by
    field_simp [ne_of_gt hs0, ne_of_gt (by positivity : 0 < s + r)]
    nlinarith
  have hfirst : 1 - r / s ≤ 1 / (2 * r ^ 2) := by
    rw [hid]
    exact one_div_le_one_div_of_le (by positivity) hprod
  have hleft :
      |r / s - (1 + r ^ 2) / r ^ 2| =
        (1 - r / s) + 1 / r ^ 2 := by
    rw [abs_of_nonpos]
    · field_simp
      ring
    · have hle : r / s ≤ 1 := (div_le_one hs0).2 hrs
      have hfrac : 1 ≤ (1 + r ^ 2) / r ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hr0)]
        nlinarith
      linarith
  change |r / s - (1 + r ^ 2) / r ^ 2| ≤
    2 * (1 + r ^ 2)⁻¹
  rw [hleft]
  have hsumBound :
      (1 - r / s) + 1 / r ^ 2 ≤ 3 / (2 * r ^ 2) := by
    calc
      (1 - r / s) + 1 / r ^ 2 ≤
          1 / (2 * r ^ 2) + 1 / r ^ 2 := by linarith
      _ = 3 / (2 * r ^ 2) := by field_simp; ring
  have hcompare :
      3 / (2 * r ^ 2) ≤ 2 * (1 + r ^ 2)⁻¹ := by
    change 3 / (2 * r ^ 2) ≤ 2 / (1 + r ^ 2)
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * r ^ 2)
      (by positivity : 0 < 1 + r ^ 2)]
    nlinarith [sq_nonneg r]
  exact hsumBound.trans hcompare

theorem weightedMonopoleCancellation_memLp_two :
    MemLp weightedMonopoleCancellation 2 halfLineMeasure := by
  apply (memLp_two_iff_integrable_sq
    weightedMonopoleCancellation_continuous.aestronglyMeasurable.restrict).2
  change IntegrableOn
    (fun r : ℝ => weightedMonopoleCancellation r ^ 2) (Ioi 0)
  have hcore : IntegrableOn
      (fun r : ℝ => weightedMonopoleCancellation r ^ 2)
      (Ioc (0 : ℝ) 2) :=
    (weightedMonopoleCancellation_continuous.pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun r : ℝ => 4 * (1 + r ^ 2)⁻¹) (Ioi 2) :=
    (integrable_inv_one_add_sq.const_mul 4).integrableOn
  have htail : IntegrableOn
      (fun r : ℝ => weightedMonopoleCancellation r ^ 2)
      (Ioi 2) := by
    refine hmajor.mono'
      (weightedMonopoleCancellation_continuous.pow 2).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := weightedMonopoleCancellation_norm_far_le r hr
    have ha0 : 0 ≤ weightedGreenDecay r := weightedGreenDecay_nonneg r
    have ha1 : weightedGreenDecay r ≤ 1 := by
      unfold weightedGreenDecay
      exact (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
        (by nlinarith [sq_nonneg r])
    have hsquare := mul_self_le_mul_self
      (norm_nonneg (weightedMonopoleCancellation r)) hb
    rw [Real.norm_eq_abs] at hsquare
    calc
      weightedMonopoleCancellation r ^ 2 =
          |weightedMonopoleCancellation r| *
            |weightedMonopoleCancellation r| := by
        rw [← sq_abs]
        ring
      _ ≤ (2 * weightedGreenDecay r) *
          (2 * weightedGreenDecay r) := hsquare
      _ ≤ 4 * (1 + r ^ 2)⁻¹ := by
        unfold weightedGreenDecay at ha0 ha1 ⊢
        nlinarith [mul_self_le_mul_self ha0 ha1]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
  exact hcore.union htail

def weightedMonopoleCancellationL2 : RealL2 halfLineMeasure :=
  weightedMonopoleCancellation_memLp_two.toLp weightedMonopoleCancellation

theorem weightedMonopoleCancellationL2_ae :
    (weightedMonopoleCancellationL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedMonopoleCancellation :=
  weightedMonopoleCancellation_memLp_two.coeFn_toLp

/-- The compactly supported curvature produced by the affine cutoff after
conjugation. -/
def weightedAffineCurvature (r : ℝ) : ℝ :=
  (1 + r ^ 2) * deriv (deriv model) r

theorem weightedAffineCurvature_continuous :
    Continuous weightedAffineCurvature := by
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold weightedAffineCurvature
  exact (continuous_const.add (continuous_id.pow 2)).mul hq2.continuous

theorem weightedAffineCurvature_zero_of_two_lt
    (r : ℝ) (hr : 2 < r) :
    weightedAffineCurvature r = 0 := by
  rw [weightedAffineCurvature,
    model_second_deriv_eq_zero_of_two_lt r hr, mul_zero]

theorem weightedAffineCurvature_memLp_two :
    MemLp weightedAffineCurvature 2 halfLineMeasure := by
  apply (memLp_two_iff_integrable_sq
    weightedAffineCurvature_continuous.aestronglyMeasurable.restrict).2
  change IntegrableOn (fun r : ℝ => weightedAffineCurvature r ^ 2) (Ioi 0)
  have hcore : IntegrableOn
      (fun r : ℝ => weightedAffineCurvature r ^ 2) (Ioc (0 : ℝ) 2) :=
    (weightedAffineCurvature_continuous.pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have htail : IntegrableOn
      (fun r : ℝ => weightedAffineCurvature r ^ 2) (Ioi 2) := by
    refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro r hr
    change 0 = weightedAffineCurvature r ^ 2
    rw [weightedAffineCurvature_zero_of_two_lt r hr, zero_pow]
    norm_num
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
  exact hcore.union htail

def weightedAffineCurvatureL2 : RealL2 halfLineMeasure :=
  weightedAffineCurvature_memLp_two.toLp weightedAffineCurvature

theorem weightedAffineCurvatureL2_ae :
    (weightedAffineCurvatureL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedAffineCurvature :=
  weightedAffineCurvature_memLp_two.coeFn_toLp

/-- The exact conjugated right-hand side of the corrected monopole
equation. -/
def weightedMonopoleDatum (ell : ℝ) (r : ℝ) : ℝ :=
  (1 + r ^ 2) * monopoleCorrectedSource ell r

/-- Its `L²` realization, assembled only after the leading logarithmic
cancellation has been made. -/
def weightedMonopoleDatumL2 (ell : ℝ) : RealL2 halfLineMeasure :=
  weightedMonopoleCancellationL2 +
    (9 : ℝ) • weightedLogModelL2 +
    ell • weightedAffineCurvatureL2 +
    (9 * ell) • weightedAffineModelL2 +
    weightedHartreeOperator weightedLogModelL2 +
    ell • weightedHartreeOperator weightedAffineModelL2

theorem weightedMonopoleDatumL2_ae (ell : ℝ) :
    (weightedMonopoleDatumL2 ell : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedMonopoleDatum ell := by
  filter_upwards [
    Lp.coeFn_add weightedMonopoleCancellationL2
      ((9 : ℝ) • weightedLogModelL2),
    Lp.coeFn_add
      (weightedMonopoleCancellationL2 +
        (9 : ℝ) • weightedLogModelL2)
      (ell • weightedAffineCurvatureL2),
    Lp.coeFn_add
      (weightedMonopoleCancellationL2 +
          (9 : ℝ) • weightedLogModelL2 +
        ell • weightedAffineCurvatureL2)
      ((9 * ell) • weightedAffineModelL2),
    Lp.coeFn_add
      (weightedMonopoleCancellationL2 +
            (9 : ℝ) • weightedLogModelL2 +
          ell • weightedAffineCurvatureL2 +
        (9 * ell) • weightedAffineModelL2)
      (weightedHartreeOperator weightedLogModelL2),
    Lp.coeFn_add
      (weightedMonopoleCancellationL2 +
              (9 : ℝ) • weightedLogModelL2 +
            ell • weightedAffineCurvatureL2 +
          (9 * ell) • weightedAffineModelL2 +
        weightedHartreeOperator weightedLogModelL2)
      (ell • weightedHartreeOperator weightedAffineModelL2),
    weightedMonopoleCancellationL2_ae,
    Lp.coeFn_smul (9 : ℝ) weightedLogModelL2,
    weightedLogModelL2_ae,
    Lp.coeFn_smul ell weightedAffineCurvatureL2,
    weightedAffineCurvatureL2_ae,
    Lp.coeFn_smul (9 * ell) weightedAffineModelL2,
    weightedAffineModelL2_ae,
    weightedHartreeOperator_log_ae,
    Lp.coeFn_smul ell
      (weightedHartreeOperator weightedAffineModelL2),
    weightedHartreeOperator_affine_ae] with r
      hadd1 hadd2 hadd3 hadd4 hadd5
      hcancel h9log hlog hellcurv hcurv h9ellaff haff
      hhoplog hellhopaff hhopaff
  simp only [Pi.add_apply] at hadd1 hadd2 hadd3 hadd4 hadd5
  simp only [Pi.smul_apply, smul_eq_mul] at h9log hellcurv h9ellaff hellhopaff
  simp only [weightedMonopoleDatumL2]
  rw [hadd5, hadd4, hadd3, hadd2, hadd1,
    hcancel, h9log, hlog, hellcurv, hcurv, h9ellaff, haff,
    hhoplog, hellhopaff, hhopaff]
  unfold weightedMonopoleDatum weightedMonopoleCancellation
    weightedLogModel weightedAffineCurvature weightedAffineModel
    monopoleCorrectedSource hPlusApply weightedGreenDecay potential
  field_simp [show 1 + r ^ 2 ≠ 0 by positivity]
  ring

theorem weightedMonopoleDatum_memLp_two (ell : ℝ) :
    MemLp (weightedMonopoleDatum ell) 2 halfLineMeasure := by
  exact (memLp_congr_ae (weightedMonopoleDatumL2_ae ell)).mp
    (Lp.memLp (weightedMonopoleDatumL2 ell))

end HBL.Modulation.Monopole
