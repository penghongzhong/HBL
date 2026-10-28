import HBL.InnerReconstruction.RepresentativeContinuous
import HBL.InnerReconstruction.RepresentativeBound
import HBL.InnerReconstruction.BoundedWeightedOutput
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem innerGreenRepresentative_inWeightedL2_neg
    (g : RealL2 halfLineMeasure) (sigma tau : ℝ)
    (hsigma : 3 / 2 < sigma) (htau : 1 / 2 < tau)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    InWeightedL2 (-tau) (innerGreenRepresentative g F) := by
  apply bounded_continuous_inWeightedL2_neg tau htau _
    (innerGreenRepresentative_continuous g sigma (by linarith) F hF)
    (innerGreenBound g F)
  intro r hr
  exact innerGreenRepresentative_abs_le g sigma hsigma F hF hr
end HBL.Modulation.Monopole
