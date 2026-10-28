import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedSourceGreenOperator_ae_primitive
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    (weightedSourceGreenOperator sigma hsigma
      (weightedSourceDataL2 sigma F hF) : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun r => weightedGreenDecay r * halfLineMinGreen F r := by
  have hop := operator_toLp_ae_eq_integral (weightedSourceGreenKernel sigma)
    (weightedSourceGreenKernel_memLp_two sigma hsigma) (weightedSourceDataL2 sigma F hF)
  change (weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF) : ℝ → ℝ)
    =ᵐ[halfLineMeasure] (fun r => ∫ rho, weightedSourceGreenKernel sigma r rho *
      weightedSourceDataL2 sigma F hF rho ∂halfLineMeasure) at hop
  filter_upwards [hop] with r hr
  rw [hr]
  unfold halfLineMinGreen
  change (∫ rho, weightedSourceGreenKernel sigma r rho *
    weightedSourceDataL2 sigma F hF rho ∂halfLineMeasure) =
    weightedGreenDecay r * (∫ rho, min r rho * F rho ∂halfLineMeasure)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [weightedSourceDataL2_ae sigma F hF] with rho hdata
  rw [hdata]
  unfold weightedSourceGreenKernel weightedGreenDecay
  calc
    _ = ((1 + r ^ 2)⁻¹ * min r rho * F rho) *
      (affineJapaneseDecay sigma rho * affineJapaneseWeight sigma rho) := by ring
    _ = _ := by rw [affineJapaneseDecay_mul_weight, mul_one]; ring
end HBL.Modulation.Monopole
