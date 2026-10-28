import HBL.WeightedPhaseAffineSource

/-!
# Actual normalized H-minus inner correction with unique affine charge

Given an arbitrary physical source F ∈ L^{2,sigma} for 3/2<sigma<2,
the exact Hartree phase resonance fixes a unique affine tail.  The
corrected source stays in L^{2,sigma}, and the actual compact
Hilbert-Schmidt Green/Fredholm equation has a unique normalized solution.

This is one genuine *inner component* of prop:one-layer-stage3, not
the complete original one-layer terminal. It does not yet establish the
manuscript L^{2,-sigma} output estimate or the global spatial match.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail
open HBL.L2Kernel

/-- The actual weighted Hilbert datum after affine threshold subtraction. -/
def phaseAffineCorrectedDataL2
    (sigma : ℝ) (hsigma : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (a : ℝ) :
    RealL2 halfLineMeasure :=
  weightedSourceDataL2 sigma
    (fun r => F r - a * channelAffineSource HartreeChannel.minus r)
    (phaseAffine_correctedSource_inWeightedL2 sigma hsigma F hF a)

/-- The two physical compatibility conditions yield exactly one affine
charge and one normalized solution of the actual phase Fredholm equation. -/
theorem existsUnique_phaseAffineChargedFredholmSolve
    (sigma : ℝ) (hsigmaLower : 3 / 2 < sigma)
    (hsigmaUpper : sigma < 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    ∃! a : ℝ,
      AffineTailOrthogonal HartreeChannel.minus F a ∧
        (∃! x : (1 - weightedPhaseBirman).kerᗮ,
          (1 - weightedPhaseBirman)
            (x : RealL2 halfLineMeasure) =
              weightedSourceGreenOperator sigma (by linarith)
                (phaseAffineCorrectedDataL2 sigma hsigmaUpper.le F hF a)) := by
  obtain ⟨a, ha, haUnique⟩ :=
    (secondManuscriptAffineTailEnvironment_closed
      sigma hsigmaLower hsigmaUpper HartreeChannel.minus F hF).1
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · change ∃! x : (1 - weightedPhaseBirman).kerᗮ,
      (1 - weightedPhaseBirman)
        (x : RealL2 halfLineMeasure) =
          weightedSourceGreenOperator sigma (by linarith)
            (weightedSourceDataL2 sigma
              (fun r => F r - a * channelAffineSource HartreeChannel.minus r)
              (phaseAffine_correctedSource_inWeightedL2
                sigma hsigmaUpper.le F hF a))
    exact existsUnique_phaseWeightedSourceFredholmSolve
      sigma (by linarith)
      (fun r => F r - a * channelAffineSource HartreeChannel.minus r)
      (phaseAffine_correctedSource_inWeightedL2 sigma hsigmaUpper.le F hF a)
      ha.2
  · intro a' ha'
    exact haUnique a' ha'.1

#print axioms phaseAffineCorrectedDataL2
#print axioms existsUnique_phaseAffineChargedFredholmSolve

end HBL.Modulation.Monopole
