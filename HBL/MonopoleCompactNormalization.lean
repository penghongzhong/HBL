import HBL.MonopoleFredholmNormalization
import HBL.MonopoleProfileTail
import HBL.ThresholdTestExistence

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The Riesz representative of the compact test in the weighted coordinate. -/
def compactMonopoleTest (r : ℝ) : ℝ :=
  (1 + r ^ 2) * normalizedZetaPlus r

theorem compactMonopoleTest_memLp :
    MemLp compactMonopoleTest 2 halfLineMeasure := by
  have hc : Continuous compactMonopoleTest := by
    exact (continuous_const.add (continuous_id.pow 2)).mul
      normalizedZetaPlus_contDiff_infty.continuous
  have hs : HasCompactSupport compactMonopoleTest := by
    change HasCompactSupport ((fun r : ℝ => 1 + r ^ 2) * normalizedZetaPlus)
    exact normalizedZetaPlus_hasCompactSupport.mul_left
  exact hc.memLp_of_hasCompactSupport hs

def compactMonopoleTestL2 : RealL2 halfLineMeasure :=
  compactMonopoleTest_memLp.toLp compactMonopoleTest

def compactMonopoleNormalization : RealL2 halfLineMeasure →L[ℝ] ℝ :=
  innerSL ℝ compactMonopoleTestL2

theorem compactMonopoleNormalization_scale_eq_one :
    compactMonopoleNormalization weightedScaleResonanceL2 = 1 := by
  change inner ℝ compactMonopoleTestL2 weightedScaleResonanceL2 = 1
  rw [L2.inner_def]
  calc
    (∫ r : ℝ, inner ℝ (compactMonopoleTestL2 r)
        (weightedScaleResonanceL2 r) ∂halfLineMeasure) =
      ∫ r in Ioi (0 : ℝ), normalizedZetaPlus r * resonancePlus r := by
      change (∫ r : ℝ, inner ℝ (compactMonopoleTestL2 r)
        (weightedScaleResonanceL2 r) ∂halfLineMeasure) =
        ∫ r : ℝ, normalizedZetaPlus r * resonancePlus r ∂halfLineMeasure
      apply integral_congr_ae
      filter_upwards [compactMonopoleTest_memLp.coeFn_toLp,
        weightedScaleResonanceL2_ae] with r ht hx
      change compactMonopoleTestL2 r = compactMonopoleTest r at ht
      rw [ht, hx, Real.inner_apply, weightedScaleResonance_closed]
      unfold compactMonopoleTest
      field_simp [show 1 + r ^ 2 ≠ 0 by positivity]
    _ = ∫ r in Ioc (0 : ℝ) (Real.exp 1),
        normalizedZetaPlus r * resonancePlus r := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        measurableSet_Ioi Ioc_subset_Ioi_self
      intro r hr
      have hlarge : Real.exp 1 < r := by
        exact lt_of_not_ge (fun hle => hr.2 ⟨hr.1, hle⟩)
      have hone : 1 ≤ r :=
        ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans hlarge).le
      rw [normalizedZetaPlus_zero_of_one_le r hone, zero_mul]
    _ = ∫ r in (0 : ℝ)..Real.exp 1,
        normalizedZetaPlus r * radialResonancePlus r := by
      rw [intervalIntegral.integral_of_le (Real.exp_pos 1).le]
      rfl
    _ = 1 := normalizedZetaPlus_normalized

theorem compactMonopoleNormalization_scale_ne_zero :
    compactMonopoleNormalization weightedScaleResonanceL2 ≠ 0 := by
  rw [compactMonopoleNormalization_scale_eq_one]
  norm_num

theorem compactMonopoleTest_model_zero (ell r : ℝ) :
    normalizedZetaPlus r * (monopoleLogModel r + ell * model r) = 0 := by
  by_cases hr : r ≤ 1
  · rw [monopoleLogModel_zero_of_le_one r hr, model_zero_of_le_one r hr]
    ring
  · rw [normalizedZetaPlus_zero_of_one_le r (lt_of_not_ge hr).le]
    ring

theorem compactMonopoleTest_profile_eq_remainder (r : ℝ) :
    normalizedZetaPlus r * monopoleProfile r =
      normalizedZetaPlus r * monopoleRemainder r := by
  unfold monopoleProfile
  rw [mul_add, compactMonopoleTest_model_zero, zero_add]

end HBL.Modulation.Monopole
