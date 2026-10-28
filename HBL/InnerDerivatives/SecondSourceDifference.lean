import HBL.InnerDerivatives.SecondSourceBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_second_source_difference_le (sigma : ℝ) (hsigma : sigma ≤ 2)
    (g h : RealL2 halfLineMeasure) (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    (Q P : ℝ → ℝ)
    (hQ : Q =ᵐ[halfLineMeasure] (fun r => -(weightedGreenDecay r * g r + F r)))
    (hP : P =ᵐ[halfLineMeasure] (fun r => -(weightedGreenDecay r * h r + G r))) :
    InWeightedL2 sigma (fun r => Q r - P r) ∧
    innerWeightedNorm sigma (fun r => Q r - P r) ≤
      ‖g - h‖ + ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have he : (fun r => Q r - P r) =ᵐ[halfLineMeasure]
      (fun r => -(weightedGreenDecay r * (g - h) r + (F r - G r))) := by
    filter_upwards [hQ, hP, Lp.coeFn_sub g h] with r hq hp hh
    rw [hq, hp, hh]
    simp only [Pi.sub_apply]
    ring
  have hb := inner_second_source_bound sigma hsigma (g - h) (fun r => F r - G r)
    (innerWeighted_sub_mem sigma F G hF hG) _ he
  simpa only [innerWeightedNorm_sub_eq sigma F G hF hG] using hb
end HBL.Modulation.Monopole
