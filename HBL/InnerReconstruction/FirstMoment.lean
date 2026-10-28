import HBL.InnerReconstruction.MomentWeight
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedSource_firstMoment_integrable
    (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    Integrable (fun r : ℝ => r * F r) halfLineMeasure := by
  have h := (weightedSource_momentWeight_memLp sigma hsigma).integrable_mul hF
  refine h.congr ?_
  filter_upwards with r
  change (r * affineJapaneseDecay sigma r) * (affineJapaneseWeight sigma r * F r) = r * F r
  calc
    _ = r * (affineJapaneseDecay sigma r * affineJapaneseWeight sigma r) * F r := by ring
    _ = r * F r := by rw [affineJapaneseDecay_mul_weight, mul_one]
end HBL.Modulation.Monopole
