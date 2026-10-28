import HBL.InnerEstimates.IntegralCauchySchwarz
import HBL.InnerEstimates.WeightedNormIdentity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_firstMoment_norm_le (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    (∫ r, ‖r * F r‖ ∂halfLineMeasure) ≤ innerMomentNorm sigma hsigma * innerWeightedNorm sigma F := by
  have h := inner_integral_norm_mul_le (fun r => r * affineJapaneseDecay sigma r)
    (fun r => affineJapaneseWeight sigma r * F r)
    (weightedSource_momentWeight_memLp sigma hsigma) hF
  have heq (r : ℝ) : (r * affineJapaneseDecay sigma r) *
      (affineJapaneseWeight sigma r * F r) = r * F r := by
    calc
      _ = r * (affineJapaneseDecay sigma r * affineJapaneseWeight sigma r) * F r := by ring
      _ = _ := by rw [affineJapaneseDecay_mul_weight, mul_one]
  simp_rw [heq] at h
  rw [innerWeightedNorm_eq sigma F hF]
  exact h
end HBL.Modulation.Monopole
