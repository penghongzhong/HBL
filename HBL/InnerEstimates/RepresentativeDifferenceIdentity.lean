import HBL.InnerEstimates.WeightedSubMembership
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerGreenRepresentative_sub
    (g h : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (r : ℝ) :
    innerGreenRepresentative g F r - innerGreenRepresentative h G r =
      innerGreenRepresentative (g - h) (fun rho => F rho - G rho) r := by
  have hprim : weightedGreenPrimitive (g - h) r = weightedGreenPrimitive g r - weightedGreenPrimitive h r := by
    unfold weightedGreenPrimitive
    rw [← integral_sub (weightedGreenPrimitive_integrable_kernel g r)
      (weightedGreenPrimitive_integrable_kernel h r)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub g h] with rho hsub
    rw [hsub]
    simp only [Pi.sub_apply]
    ring
  have hsource : halfLineMinGreen (fun rho => F rho - G rho) r = halfLineMinGreen F r - halfLineMinGreen G r := by
    unfold halfLineMinGreen
    rw [← integral_sub
      (halfLineMinGreen_kernel_integrable F (weightedSource_integrable sigma hsigma F hF) r)
      (halfLineMinGreen_kernel_integrable G (weightedSource_integrable sigma hsigma G hG) r)]
    apply integral_congr_ae
    filter_upwards with rho
    ring
  unfold innerGreenRepresentative
  rw [hprim, hsource]
  ring
end HBL.Modulation.Monopole
