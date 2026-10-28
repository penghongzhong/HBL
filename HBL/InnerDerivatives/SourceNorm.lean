import HBL.InnerDerivatives.Definitions
import HBL.InnerEstimates.IntegralCauchySchwarz
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_source_integral_norm_le (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    (∫ r, ‖F r‖ ∂halfLineMeasure) ≤ innerDecayNorm sigma hsigma * innerWeightedNorm sigma F := by
  have h := inner_integral_norm_mul_le (affineJapaneseDecay sigma)
    (fun r => affineJapaneseWeight sigma r * F r) (affineJapaneseDecay_memLp_two sigma hsigma) hF
  have heq (r : ℝ) : affineJapaneseDecay sigma r * (affineJapaneseWeight sigma r * F r) = F r := by
    rw [← mul_assoc, affineJapaneseDecay_mul_weight, one_mul]
  simp_rw [heq] at h
  rw [innerWeightedNorm_eq sigma F hF]
  exact h
end HBL.Modulation.Monopole
