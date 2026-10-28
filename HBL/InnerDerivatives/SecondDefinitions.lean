import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

def innerPlusSecondDerivativeConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  ‖weightedPotentialOperator‖ * innerPlusHilbertConstant sigma hLower hUpper + innerPlusCorrectionConstant sigma hLower hUpper

def innerMinusSecondDerivativeConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  3 * innerMinusHilbertConstant sigma hLower hUpper + innerMinusCorrectionConstant sigma hLower hUpper
end HBL.Modulation.Monopole
