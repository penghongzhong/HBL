import HBL.InnerReconstruction.SourceIntegrable
import HBL.InnerReconstruction.GreenLipschitz
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem innerGreenRepresentative_continuous
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    Continuous (innerGreenRepresentative g F) :=
  (weightedGreenPrimitive_continuous g).add
    (halfLineMinGreen_lipschitz F (weightedSource_integrable sigma hsigma F hF)).continuous
end HBL.Modulation.Monopole
