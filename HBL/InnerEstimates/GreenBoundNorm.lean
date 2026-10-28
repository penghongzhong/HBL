import HBL.InnerEstimates.FirstMomentNorm
import HBL.InnerEstimates.GreenPrimitiveNorm
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerGreenBound_norm_le (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    innerGreenBound g F ≤ innerGreenMajorantNorm * ‖g‖ + innerMomentNorm sigma hsigma * innerWeightedNorm sigma F :=
  add_le_add (inner_greenPrimitiveBound_le g) (inner_firstMoment_norm_le sigma hsigma F hF)
end HBL.Modulation.Monopole
