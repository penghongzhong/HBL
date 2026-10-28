import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedSource_integrable
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    Integrable F halfLineMeasure := by
  have h := (affineJapaneseDecay_memLp_two sigma hsigma).integrable_mul hF
  refine h.congr ?_
  filter_upwards with r
  change affineJapaneseDecay sigma r * (affineJapaneseWeight sigma r * F r) = F r
  rw [← mul_assoc, affineJapaneseDecay_mul_weight, one_mul]
end HBL.Modulation.Monopole
