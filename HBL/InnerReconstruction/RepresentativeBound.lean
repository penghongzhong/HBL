import HBL.InnerReconstruction.SourceIntegrable
import HBL.InnerReconstruction.FirstMoment
import HBL.InnerReconstruction.GreenBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem innerGreenRepresentative_abs_le
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) {r : ℝ} (hr : 0 < r) :
    |innerGreenRepresentative g F r| ≤ innerGreenBound g F := by
  have h0 := weightedSource_integrable sigma (by linarith) F hF
  have h1 := weightedSource_firstMoment_integrable sigma hsigma F hF
  exact (abs_add_le _ _).trans
    (_root_.add_le_add (weightedGreenPrimitive_abs_le_bound g hr)
      (halfLineMinGreen_abs_le_firstMoment F h0 h1 hr.le))
end HBL.Modulation.Monopole
