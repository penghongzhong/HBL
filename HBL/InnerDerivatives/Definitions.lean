import HBL.InnerEstimates.ActualBoundedSolvers
import Mathlib.Analysis.Calculus.FDeriv.Measurable
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

def innerGreenDerivative (g : RealL2 halfLineMeasure) (F : ℝ → ℝ) : ℝ → ℝ :=
  halfLineGreenTail (fun r => weightedGreenDecay r * g r + F r)

def innerGreenDerivativeMajorant : ℝ :=
  ‖weightedGreenDecay_memLp_two.toLp weightedGreenDecay‖ + innerGreenMajorantNorm

def innerSourceDerivativeMajorant (sigma : ℝ) (hsigma : 3 / 2 < sigma) : ℝ :=
  innerDecayNorm sigma (by linarith) + innerMomentNorm sigma hsigma

def innerPlusDerivativeConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerGreenDerivativeMajorant * ‖weightedPotentialOperator‖ * innerPlusHilbertConstant sigma hLower hUpper +
    innerSourceDerivativeMajorant sigma hLower * innerPlusCorrectionConstant sigma hLower hUpper

def innerMinusDerivativeConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerGreenDerivativeMajorant * 3 * innerMinusHilbertConstant sigma hLower hUpper +
    innerSourceDerivativeMajorant sigma hLower * innerMinusCorrectionConstant sigma hLower hUpper
end HBL.Modulation.Monopole
