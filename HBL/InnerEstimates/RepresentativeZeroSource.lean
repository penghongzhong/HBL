import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerGreenRepresentative_zero_source :
    innerGreenRepresentative (0 : RealL2 halfLineMeasure) (fun _ => 0) = fun _ => 0 := by
  funext r
  unfold innerGreenRepresentative weightedGreenPrimitive halfLineMinGreen
  simp only [mul_zero, integral_zero, add_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal)) (μ := halfLineMeasure)] with rho hrho
  rw [hrho]
  simp
end HBL.Modulation.Monopole
