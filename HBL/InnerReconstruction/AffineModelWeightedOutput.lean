import HBL.InnerReconstruction.MomentWeight
import HBL.InnerReconstruction.AffineRestorationDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem affineModel_inWeightedL2_neg (tau : ℝ) (htau : 3 / 2 < tau) :
    InWeightedL2 (-tau) model := by
  apply (weightedSource_momentWeight_memLp tau htau).norm.mono'
    (((affineJapaneseWeight_continuous (-tau)).mul
      model_contDiff_infty.continuous).aestronglyMeasurable)
  filter_upwards with r
  change ‖affineJapaneseDecay tau r * (cutoff r * r)‖ ≤ ‖r * affineJapaneseDecay tau r‖
  have hc : ‖cutoff r‖ ≤ 1 := by
    unfold cutoff
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg (r - 1))]
    exact Real.smoothTransition.le_one (r - 1)
  calc
    ‖affineJapaneseDecay tau r * (cutoff r * r)‖ = ‖cutoff r‖ * ‖r * affineJapaneseDecay tau r‖ := by
      rw [← norm_mul]
      congr 1
      ring
    _ ≤ 1 * ‖r * affineJapaneseDecay tau r‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = _ := one_mul _
end HBL.Modulation.Monopole
