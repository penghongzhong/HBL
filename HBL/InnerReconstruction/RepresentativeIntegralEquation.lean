import HBL.InnerReconstruction.SourceIntegrable
import HBL.InnerReconstruction.GreenKernelIntegrable
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem innerGreenRepresentative_eq_totalGreen
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (r : ℝ) :
    innerGreenRepresentative g F r =
      halfLineMinGreen (fun rho => weightedGreenDecay rho * g rho + F rho) r := by
  unfold innerGreenRepresentative weightedGreenPrimitive halfLineMinGreen
  change (∫ rho, min r rho * (weightedGreenDecay rho * g rho) ∂halfLineMeasure) +
      (∫ rho, min r rho * F rho ∂halfLineMeasure) = _
  rw [← integral_add (weightedGreenPrimitive_integrable_kernel g r)
    (halfLineMinGreen_kernel_integrable F (weightedSource_integrable sigma hsigma F hF) r)]
  apply integral_congr_ae
  filter_upwards with rho
  ring
end HBL.Modulation.Monopole
