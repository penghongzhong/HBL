import HBL.InnerEstimates.IntegralCauchySchwarz
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_greenPrimitiveBound_le (g : RealL2 halfLineMeasure) :
    weightedGreenPrimitiveBound g ≤ innerGreenMajorantNorm * ‖g‖ := by
  have h := inner_integral_norm_mul_le weightedGreenOutputMajorant g
    weightedGreenOutputMajorant_memLp_two (Lp.memLp g)
  simpa only [weightedGreenPrimitiveBound, innerGreenMajorantNorm, Lp.toLp_coeFn] using h
end HBL.Modulation.Monopole
