import HBL.InnerDerivatives.SecondDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_weighted_potential_norm_le (sigma : ℝ) (hsigma : sigma ≤ 2) (g : RealL2 halfLineMeasure) :
    InWeightedL2 sigma (fun r => weightedGreenDecay r * g r) ∧
    innerWeightedNorm sigma (fun r => weightedGreenDecay r * g r) ≤ ‖g‖ := by
  have hpoint (r : ℝ) : ‖affineJapaneseWeight sigma r * (weightedGreenDecay r * g r)‖ ≤ ‖g r‖ := by
    have hw : affineJapaneseWeight sigma r ≤ 1 + r ^ 2 := by
      calc
        _ ≤ (1 + r ^ 2) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg r]) (by linarith)
        _ = _ := Real.rpow_one _
    have hmul : affineJapaneseWeight sigma r * weightedGreenDecay r ≤ 1 := by
      calc
        _ ≤ (1 + r ^ 2) * weightedGreenDecay r := mul_le_mul_of_nonneg_right hw (weightedGreenDecay_nonneg r)
        _ = 1 := mul_inv_cancel₀ (by positivity)
    rw [← mul_assoc, norm_mul, Real.norm_of_nonneg (show 0 ≤ affineJapaneseWeight sigma r * weightedGreenDecay r by
      unfold affineJapaneseWeight weightedGreenDecay; positivity)]
    exact (mul_le_mul_of_nonneg_right hmul (norm_nonneg _)).trans_eq (one_mul _)
  have hmem : InWeightedL2 sigma (fun r => weightedGreenDecay r * g r) := by
    apply (Lp.memLp g).mono
      ((affineJapaneseWeight_continuous sigma).aestronglyMeasurable.mul
        (weightedGreenDecay_continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)))
    exact Eventually.of_forall hpoint
  refine ⟨hmem, ?_⟩
  rw [innerWeightedNorm_eq sigma _ hmem]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [weightedSourceDataL2_ae sigma _ hmem] with r hr
  rw [hr]
  exact hpoint r
end HBL.Modulation.Monopole
