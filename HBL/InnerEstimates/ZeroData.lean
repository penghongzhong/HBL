import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeightedData_zero (sigma : ℝ) (h0 : InWeightedL2 sigma (fun _ => 0)) :
    weightedSourceDataL2 sigma (fun _ => 0) h0 = 0 := by
  apply Lp.ext
  filter_upwards [weightedSourceDataL2_ae sigma (fun _ => 0) h0,
    Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal)) (μ := halfLineMeasure)] with r hr hz
  rw [hr, hz]
  simp
end HBL.Modulation.Monopole
