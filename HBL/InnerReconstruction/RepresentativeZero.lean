import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem innerGreenRepresentative_zero
    (g : RealL2 halfLineMeasure) (F : ℝ → ℝ) :
    innerGreenRepresentative g F 0 = 0 := by
  have hg : weightedGreenPrimitive g 0 = 0 :=
    halfLineMinGreen_zero (fun r => weightedGreenDecay r * g r)
  simp only [innerGreenRepresentative, hg, halfLineMinGreen_zero, add_zero]
end HBL.Modulation.Monopole
