import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedInnerClassical
import HBL.InnerEstimates.PlusRemainderDifference
import HBL.InnerDerivatives.RemainderZero
import HBL.InnerEstimates.WeightedNormNonnegative
import HBL.HartreeTailLeakage
import Mathlib.Tactic

/-!
A genuine relative factor for a fixed normalized inner inverse.
Cutting off its affine output changes the real-channel Hessian by the
actual nonlocal outer tail, while the imaginary-channel Hessian stays
exact on the core.  The tail is bounded by R^(-2) times the ORIGINAL
weighted source norm, using the already constructed Fredholm inverse
and its forced charge.  There is no assigned order or assumed small
response norm.

This is the core part of the linearized cutoff defect.  The moving
cutoff annulus, time derivative, change of background Hessian and full
nonlinear remainder are separate parts of the physical correction.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

def actualInnerCutoffResponse (R : ℝ) (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 - cutoff (r / R)) * q r

def actualInnerCutoffOuterTail (R : ℝ) (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  cutoff (r / R) * q r

/-- Fixed inverse and resonance constants, independent of source and radius. -/
def actualInnerPlusLinearGrowthConstant : ℝ :=
  |innerPlusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)| +
    2 * ‖weightedSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖

def actualInnerCutoffRelativeConstant : ℝ :=
  16 * Real.pi * hartreeKappa * actualInnerPlusLinearGrowthConstant

private theorem actual_inner_plus_growth_constant_nonneg :
    0 ≤ actualInnerPlusLinearGrowthConstant := by
  unfold actualInnerPlusLinearGrowthConstant
  positivity

private theorem actual_inner_cutoff_relative_constant_nonneg :
    0 ≤ actualInnerCutoffRelativeConstant := by
  have hc := actual_inner_plus_growth_constant_nonneg
  unfold actualInnerCutoffRelativeConstant hartreeKappa
  positivity

private theorem actual_normalized_plus_linear_growth
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F)
    (r : ℝ) (hr : 2 ≤ r) :
    |normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF r| ≤
      actualInnerPlusLinearGrowthConstant * innerWeightedNorm (7 / 4 : ℝ) F * r := by
  let A : ℝ := innerPlusRemainderConstant (7 / 4 : ℝ) (by norm_num) (by norm_num)
  let B : ℝ := 2 * ‖weightedSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) F
  have hN : 0 ≤ N := innerWeightedNorm_nonneg _ _
  have hr0 : 0 < r := by linarith
  have h0 : InWeightedL2 (7 / 4 : ℝ) (fun _ => 0) := by
    simp [InWeightedL2]
  have hrem := normalizedPlusRemainder_difference_le
    (7 / 4 : ℝ) (by norm_num) (by norm_num) F (fun _ => 0) hF h0 hr0
  rw [(normalizedRemainder_zero (7 / 4 : ℝ) (by norm_num) (by norm_num) h0).1,
    innerWeightedData_zero] at hrem
  have hrem' :
      |normalizedPlusRemainder (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF r| ≤
        A * N := by
    simpa only [sub_zero, Real.norm_eq_abs,
      ← innerWeightedNorm_eq (7 / 4 : ℝ) F hF] using hrem
  have hremAbs :
      |normalizedPlusRemainder (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF r| ≤
        |A| * N := hrem'.trans
    (mul_le_mul_of_nonneg_right (le_abs_self A) hN)
  have hcharge := actualPlusCharge_difference_le
    (7 / 4 : ℝ) (by norm_num) F (fun _ => 0) hF h0
  have hzero : actualPlusCharge (fun _ => 0) = 0 := by
    simp [actualPlusCharge, channelPairing]
  rw [hzero, innerWeightedData_zero] at hcharge
  have ha : |actualPlusCharge F| ≤ B * N := by
    simpa only [sub_zero, Real.norm_eq_abs,
      ← innerWeightedNorm_eq (7 / 4 : ℝ) F hF] using hcharge
  have hmul : |A| * N ≤ |A| * N * r :=
    le_mul_of_one_le_right (mul_nonneg (abs_nonneg A) hN) (by linarith)
  change |normalizedPlusRemainder (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF r +
      actualPlusCharge F * model r| ≤ (|A| + B) * N * r
  rw [model_eq_id_of_two_le r hr]
  calc
    _ ≤ |normalizedPlusRemainder (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF r| +
        |actualPlusCharge F * r| := abs_add_le _ _
    _ ≤ |A| * N + (B * N) * r := by
      rw [abs_mul, abs_of_pos hr0]
      exact add_le_add hremAbs (mul_le_mul_of_nonneg_right ha hr0.le)
    _ ≤ |A| * N * r + (B * N) * r := add_le_add hmul le_rfl
    _ = _ := by ring

private theorem actual_inner_cutoff_eq_near
    (q : ℝ → ℝ) (R r : ℝ) (hR : 0 < R) (hr : r < R) :
    actualInnerCutoffResponse R q =ᶠ[𝓝 r] q := by
  filter_upwards [Iio_mem_nhds hr] with x hx
  have harg : x / R ≤ 1 := (div_le_one hR).2 hx.le
  simp only [actualInnerCutoffResponse, cutoff_zero_of_le_one _ harg,
    sub_zero, one_mul]

private theorem actual_inner_outer_tail_control
    (q : ℝ → ℝ) (hq : Continuous q) (R r M : ℝ)
    (hM : 0 ≤ M) (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hbound : ∀ rho : ℝ, R ≤ rho → |q rho| ≤ M * rho) :
    IntegrableOn (fun rho => hartreeKernel r rho * actualInnerCutoffOuterTail R q rho)
      (Ioi (0 : ℝ)) ∧
      |nonlocalApply (actualInnerCutoffOuterTail R q) r| ≤
        16 * Real.pi * hartreeKappa * M * r * bubble r ^ 3 / R ^ 2 := by
  have hc : Continuous (actualInnerCutoffOuterTail R q) :=
    (cutoff_contDiff_infty.continuous.comp (continuous_id.div_const R)).mul hq
  have hb : ∀ rho : ℝ, R ≤ rho →
      |actualInnerCutoffOuterTail R q rho| ≤ M * rho := by
    intro rho hrho
    unfold actualInnerCutoffOuterTail
    rw [abs_mul, abs_of_nonneg
      (show 0 ≤ cutoff (rho / R) from Real.smoothTransition.nonneg _)]
    exact (mul_le_mul_of_nonneg_right
      (show cutoff (rho / R) ≤ 1 from Real.smoothTransition.le_one _)
      (abs_nonneg (q rho))).trans (by simpa only [one_mul] using hbound rho hrho)
  have ht := hartree_tail_linear_bound (actualInnerCutoffOuterTail R q)
    hc.measurable hM hr hR hsep hb
  let f : ℝ → ℝ := fun rho => hartreeKernel r rho * actualInnerCutoffOuterTail R q rho
  have he : f = (Ioi R).indicator f := by
    funext rho
    by_cases hh : rho ∈ Ioi R
    · rw [indicator_of_mem hh]
    · rw [indicator_of_notMem hh]
      have harg : rho / R ≤ 1 := (div_le_one hR).2 (le_of_not_gt hh)
      simp only [f, actualInnerCutoffOuterTail,
        cutoff_zero_of_le_one _ harg, zero_mul, mul_zero]
  have hi : IntegrableOn ((Ioi R).indicator f) (Ioi (0 : ℝ)) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi]
    change Integrable f ((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi R))
    rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hR.le)]
    exact ht.1
  have hfull : IntegrableOn f (Ioi (0 : ℝ)) :=
    hi.congr_fun (fun rho _ => congrFun he.symm rho) measurableSet_Ioi
  refine ⟨hfull, ?_⟩
  have heint : (∫ rho in Ioi (0 : ℝ), f rho) = ∫ rho in Ioi R, f rho := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ), (Ioi R).indicator f rho :=
        integral_congr_ae (Eventually.of_forall (fun rho => congrFun he rho))
      _ = _ := by
        rw [integral_indicator measurableSet_Ioi,
          Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hR.le)]
  change |∫ rho in Ioi (0 : ℝ), f rho| ≤ _
  rw [heint]
  exact ht.2

/-- A source-norm relative R^(-2) gain for the actual cutoff Hessian defect.
The fixed source is arbitrary continuous weighted data, and every response,
charge and nonlocal error is its actual normalized Fredholm construction.
The result is on the separated core, not on the moving cutoff annulus. -/
theorem actual_Hartree_normalized_inner_cutoff_relative_gain
    (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F) (hcF : Continuous F)
    (R r : ℝ) (hR : 2 ≤ R) (hr : 0 < r) (hsep : r ≤ R / 2) :
    let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
    hMinusApply (actualInnerCutoffResponse R qm) r = F r ∧
      hPlusApply (actualInnerCutoffResponse R qp) r =
        F r + nonlocalApply (actualInnerCutoffOuterTail R qp) r ∧
      IntegrableOn (fun rho => hartreeKernel r rho * actualInnerCutoffOuterTail R qp rho)
        (Ioi (0 : ℝ)) ∧
      |(hPlusApply (actualInnerCutoffResponse R qp) r - F r) / r| ≤
        (actualInnerCutoffRelativeConstant / R ^ 2) *
          innerWeightedNorm (7 / 4 : ℝ) F * bubble r ^ 3 ∧
      |hPlusApply (actualInnerCutoffResponse R qp) r - F r| ≤
        (actualInnerCutoffRelativeConstant / R ^ 2) * innerWeightedNorm (7 / 4 : ℝ) F := by
  let qp := normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
  let qm := normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) F
  let M : ℝ := actualInnerPlusLinearGrowthConstant * N
  have hN : 0 ≤ N := innerWeightedNorm_nonneg _ _
  have hM : 0 ≤ M := mul_nonneg actual_inner_plus_growth_constant_nonneg hN
  have hC : 0 ≤ actualInnerCutoffRelativeConstant :=
    actual_inner_cutoff_relative_constant_nonneg
  have hRpos : 0 < R := by linarith
  have hrR : r < R := by linarith
  have hp := normalizedPlusOutput_properties
    (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF
  have htail := actual_inner_outer_tail_control qp hp.1 R r M hM hRpos hr
    (by linarith) (fun rho hrho => actual_normalized_plus_linear_growth F hF rho (hR.trans hrho))
  have hpMem : MemLp (fun rho => weightedGreenDecay rho * qp rho) 2 halfLineMeasure := by
    have hw : InWeightedL2 (-(2 : ℝ)) qp := hp.2.2.1 2 (by norm_num)
    simpa [InWeightedL2, affineJapaneseWeight, weightedGreenDecay, Real.rpow_neg_one] using hw
  have hpInt := nonlocalApply_integrable_of_weighted_memLp qp hpMem hr.le
  have hnearP := actual_inner_cutoff_eq_near qp R r hRpos hrR
  have hnearM := actual_inner_cutoff_eq_near qm R r hRpos hrR
  have hnonlocal : nonlocalApply (actualInnerCutoffResponse R qp) r =
      nonlocalApply qp r - nonlocalApply (actualInnerCutoffOuterTail R qp) r := by
    unfold nonlocalApply
    rw [← integral_sub hpInt htail.1]
    congr 1
    funext rho
    unfold actualInnerCutoffResponse actualInnerCutoffOuterTail
    ring
  have hmEq : hMinusApply (actualInnerCutoffResponse R qm) r = F r := by
    have hmClass := (normalizedMinusOutput_classical
      (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF hcF r hr).2.2
    calc
      _ = hMinusApply qm r := by
        unfold hMinusApply
        rw [hnearM.deriv.deriv_eq, hnearM.eq_of_nhds]
      _ = _ := hmClass
  have hpEq : hPlusApply (actualInnerCutoffResponse R qp) r =
      F r + nonlocalApply (actualInnerCutoffOuterTail R qp) r := by
    have hpClass := (normalizedPlusOutput_classical
      (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF hcF r hr).2.2
    calc
      _ = hPlusApply qp r + nonlocalApply (actualInnerCutoffOuterTail R qp) r := by
        unfold hPlusApply
        rw [hnearP.deriv.deriv_eq, hnearP.eq_of_nhds, hnonlocal]
        ring
      _ = _ := by rw [hpClass]
  have ht : |nonlocalApply (actualInnerCutoffOuterTail R qp) r| ≤
      (actualInnerCutoffRelativeConstant * N / R ^ 2) * (r * bubble r ^ 3) := by
    convert htail.2 using 1
    dsimp [actualInnerCutoffRelativeConstant, M]
    ring
  have hgeom : r * bubble r ^ 3 ≤ 1 := by
    have hsq : bubble r ^ 2 ≤ 1 := pow_le_one₀ (bubble_nonneg r) (bubble_le_one r)
    calc
      r * bubble r ^ 3 = (r * bubble r) * bubble r ^ 2 := by ring
      _ ≤ 1 * 1 := mul_le_mul (radius_mul_bubble_le_one hr.le) hsq
        (sq_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  dsimp only
  refine ⟨hmEq, hpEq, htail.1, ?_, ?_⟩
  · rw [hpEq, add_sub_cancel_left, abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hr).2
    exact ht.trans_eq (by ring)
  · rw [hpEq, add_sub_cancel_left]
    calc
      _ ≤ (actualInnerCutoffRelativeConstant * N / R ^ 2) * (r * bubble r ^ 3) := ht
      _ ≤ (actualInnerCutoffRelativeConstant * N / R ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = _ := by ring

end HBL.TypeIIDynamicSelection
