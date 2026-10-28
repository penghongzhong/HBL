import HBL.ActualInnerAffineEstimates
import HBL.InnerReconstruction.ActualClassicalAffineSolution
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

/-- The real weighted L2 norm; estimates below always establish or assume membership. -/
def innerWeightedNorm (sigma : ℝ) (F : ℝ → ℝ) : ℝ :=
  (eLpNorm (fun r => affineJapaneseWeight sigma r * F r) 2 halfLineMeasure).toReal

def innerDecayNorm (tau : ℝ) (htau : 1 / 2 < tau) : ℝ :=
  ‖(affineJapaneseDecay_memLp_two tau htau).toLp (affineJapaneseDecay tau)‖

def innerMomentNorm (sigma : ℝ) (hsigma : 3 / 2 < sigma) : ℝ :=
  ‖(weightedSource_momentWeight_memLp sigma hsigma).toLp
    (fun r => r * affineJapaneseDecay sigma r)‖

def innerGreenMajorantNorm : ℝ :=
  ‖weightedGreenOutputMajorant_memLp_two.toLp weightedGreenOutputMajorant‖

def innerFredholmConstant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K : E →L[ℝ] E) (hK : IsCompactOperator K) : NNReal :=
  Classical.choose (HBL.Fredholm.one_sub_antilipschitz_on_kernelComplement hK)

def normalizedPlusInner (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : (1 - weightedBirmanSchwingerOperator).kerᗮ :=
  weightedSourceFredholmSolution sigma (by linarith) (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
    (actualPlusCharge_orthogonal sigma (by linarith) F hF).2

def normalizedMinusInner (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : (1 - weightedPhaseBirman).kerᗮ :=
  Classical.choose (existsUnique_phaseWeightedSourceFredholmSolve sigma (by linarith)
    (correctedMinusSource F) (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
    (actualMinusCharge_orthogonal sigma (by linarith) F hF).2)

def normalizedPlusRemainder (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : ℝ → ℝ :=
  innerGreenRepresentative (weightedPotentialOperator (normalizedPlusInner sigma hLower hUpper F hF))
    (correctedPlusSource F)

def normalizedMinusRemainder (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : ℝ → ℝ :=
  innerGreenRepresentative ((3 : ℝ) • (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure))
    (correctedMinusSource F)

def normalizedPlusOutput (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : ℝ → ℝ :=
  affineRestore (normalizedPlusRemainder sigma hLower hUpper F hF) (actualPlusCharge F)

def normalizedMinusOutput (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : ℝ → ℝ :=
  affineRestore (normalizedMinusRemainder sigma hLower hUpper F hF) (actualMinusCharge F)

def innerPlusCorrectionConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  1 + 2 * ‖weightedSourceResonanceL2 sigma (by linarith)‖ * ‖plusAffineSourceDataL2 sigma hUpper.le‖

def innerMinusCorrectionConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  1 + ‖weightedPhaseSourceResonanceL2 sigma (by linarith)‖ * ‖minusAffineSourceDataL2 sigma hUpper.le‖

def innerPlusHilbertConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerFredholmConstant weightedBirmanSchwingerOperator weightedBirmanSchwingerOperator_compact *
    ‖weightedSourceGreenOperator sigma (by linarith)‖ * innerPlusCorrectionConstant sigma hLower hUpper

def innerMinusHilbertConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerFredholmConstant weightedPhaseBirman weightedPhaseBirman_compact *
    ‖weightedSourceGreenOperator sigma (by linarith)‖ * innerMinusCorrectionConstant sigma hLower hUpper

def innerPlusRemainderConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerGreenMajorantNorm * ‖weightedPotentialOperator‖ * innerPlusHilbertConstant sigma hLower hUpper +
    innerMomentNorm sigma hLower * innerPlusCorrectionConstant sigma hLower hUpper

def innerMinusRemainderConstant (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) : ℝ :=
  innerGreenMajorantNorm * 3 * innerMinusHilbertConstant sigma hLower hUpper +
    innerMomentNorm sigma hLower * innerMinusCorrectionConstant sigma hLower hUpper
end HBL.Modulation.Monopole
