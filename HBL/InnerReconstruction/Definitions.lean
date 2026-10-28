import HBL.ActualInnerAffinelyCorrected
import HBL.MonopoleFredholmTail
import HBL.WeightedFreeGreenODE
import HBL.L2KernelPointwise

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Original-variable representative of the potential and external source. -/
def innerGreenRepresentative (g : RealL2 halfLineMeasure) (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  weightedGreenPrimitive g r + halfLineMinGreen F r

def innerGreenBound (g : RealL2 halfLineMeasure) (F : ℝ → ℝ) : ℝ :=
  weightedGreenPrimitiveBound g + ∫ rho, ‖rho * F rho‖ ∂halfLineMeasure

def sourceGreenLipschitzConstant (F : ℝ → ℝ) : NNReal where
  val := ∫ rho, ‖F rho‖ ∂halfLineMeasure
  property := integral_nonneg fun _ => norm_nonneg _

end HBL.Modulation.Monopole
