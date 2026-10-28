import HBL.InnerDerivatives.WeightedAETransfer
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem affineRestore_second_weighted_bound (sigma : ℝ) (q : ℝ → ℝ) (a : ℝ)
    (hq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ q r)
    (hdq : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv q) r)
    (hmem : InWeightedL2 sigma (deriv (deriv q))) :
    InWeightedL2 sigma (deriv (deriv (affineRestore q a))) ∧
    innerWeightedNorm sigma (deriv (deriv (affineRestore q a))) ≤
      innerWeightedNorm sigma (deriv (deriv q)) + ‖a‖ * innerWeightedNorm sigma affineModelSecondDerivative := by
  have hb := innerWeighted_sub_const_mul_bound sigma (deriv (deriv q)) affineModelSecondDerivative
    hmem (affineModelSecondDerivative_inWeightedL2 sigma) (-a)
  have he : (fun r => deriv (deriv q) r - (-a) * affineModelSecondDerivative r) =ᵐ[halfLineMeasure]
      deriv (deriv (affineRestore q a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [(affineRestore_second_hasDerivAt q a hq hdq hr).deriv]
    unfold affineModelSecondDerivative
    ring
  have ht := innerWeighted_ae_transfer sigma _ _ hb.1 he
  refine ⟨ht.1, ?_⟩
  rw [ht.2]
  simpa only [norm_neg] using hb.2
end HBL.Modulation.Monopole
