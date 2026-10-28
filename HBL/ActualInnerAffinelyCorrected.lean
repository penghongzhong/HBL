import HBL.ActualInnerTwoChannel
import HBL.WeightedPlusAffineComplete
import HBL.WeightedPhaseAffineSource
import Mathlib.Tactic

/-!
# Actual affine-corrected H-plus / H-minus inner corrections

The two unique real threshold charges are specified by their genuine
physical resonance pairings.  For every L^{2,sigma} source with
3/2 < sigma < 2, the corrected sources belong to the same class,
have zero physical threshold charge, and admit a *unique pair* of
normalized solutions of the true weighted Birman-Schwinger equations.

This is not the original full one-layer PDE residual theorem: Kummer,
remote, cutoff commutators, and quantitative generated-order estimates
still have to be instantiated and assembled.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Profile.ActualInner

open HBL.L2Kernel
open HBL.Modulation.AffineTail
open HBL.Modulation.Monopole

/-- The unique real-channel affine slope. -/
def actualPlusCharge (F : ℝ → ℝ) : ℝ :=
  -(channelPairing HartreeChannel.plus F) / channelLimit HartreeChannel.plus

/-- The unique phase-channel affine slope. -/
def actualMinusCharge (F : ℝ → ℝ) : ℝ :=
  -(channelPairing HartreeChannel.minus F) / channelLimit HartreeChannel.minus

def correctedPlusSource (F : ℝ → ℝ) : ℝ → ℝ :=
  fun r => F r - actualPlusCharge F * channelAffineSource HartreeChannel.plus r

def correctedMinusSource (F : ℝ → ℝ) : ℝ → ℝ :=
  fun r => F r - actualMinusCharge F * channelAffineSource HartreeChannel.minus r

theorem actualPlusCharge_orthogonal
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    AffineTailOrthogonal HartreeChannel.plus F (actualPlusCharge F) := by
  exact (affineTailOrthogonal_iff_charge_formula
    HartreeChannel.plus sigma hsigma F hF (actualPlusCharge F)).2 rfl

theorem actualMinusCharge_orthogonal
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    AffineTailOrthogonal HartreeChannel.minus F (actualMinusCharge F) := by
  exact (affineTailOrthogonal_iff_charge_formula
    HartreeChannel.minus sigma hsigma F hF (actualMinusCharge F)).2 rfl

theorem actualPlusCharge_unique
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (a : ℝ) (ha : AffineTailOrthogonal HartreeChannel.plus F a) :
    a = actualPlusCharge F :=
  (affineTailOrthogonal_iff_charge_formula
    HartreeChannel.plus sigma hsigma F hF a).1 ha

theorem actualMinusCharge_unique
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (a : ℝ) (ha : AffineTailOrthogonal HartreeChannel.minus F a) :
    a = actualMinusCharge F :=
  (affineTailOrthogonal_iff_charge_formula
    HartreeChannel.minus sigma hsigma F hF a).1 ha

theorem correctedPlusSource_memWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    InWeightedL2 sigma (correctedPlusSource F) := by
  exact hPlusAffineCorrectedSource_inWeightedL2
    sigma hsigma F hF (actualPlusCharge F)

theorem correctedMinusSource_memWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    InWeightedL2 sigma (correctedMinusSource F) := by
  exact phaseAffine_correctedSource_inWeightedL2
    sigma hsigma F hF (actualMinusCharge F)

theorem actualAffine_corrected_sources_compatible
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (Fplus Fminus : ℝ → ℝ)
    (hp : InWeightedL2 sigma Fplus)
    (hm : InWeightedL2 sigma Fminus) :
    channelPairing HartreeChannel.plus (correctedPlusSource Fplus) = 0 ∧
    channelPairing HartreeChannel.minus (correctedMinusSource Fminus) = 0 := by
  exact ⟨(actualPlusCharge_orthogonal sigma hsigma Fplus hp).2,
    (actualMinusCharge_orthogonal sigma hsigma Fminus hm).2⟩

/-- Both actual normalized weighted Fredholm solutions exist uniquely
after removing the two uniquely forced *physical* affine charges. -/
theorem existsUnique_actualInner_affinelyCorrected
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (Fplus Fminus : ℝ → ℝ)
    (hp : InWeightedL2 sigma Fplus)
    (hm : InWeightedL2 sigma Fminus) :
    ∃! x : InnerCorrections,
      (1 - weightedBirmanSchwingerOperator)
          (x.1 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma
            (correctedPlusSource Fplus)
            (correctedPlusSource_memWeightedL2 sigma hUpper.le Fplus hp)) ∧
      (1 - weightedPhaseBirman)
          (x.2 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma (by linarith)
          (weightedSourceDataL2 sigma
            (correctedMinusSource Fminus)
            (correctedMinusSource_memWeightedL2 sigma hUpper.le Fminus hm)) := by
  have hp0 :=
    correctedPlusSource_memWeightedL2 sigma hUpper.le Fplus hp
  have hm0 :=
    correctedMinusSource_memWeightedL2 sigma hUpper.le Fminus hm
  have hcharges :=
    actualAffine_corrected_sources_compatible sigma (by linarith)
      Fplus Fminus hp hm
  exact existsUnique_actual_twoChannel_compatible_solve
    sigma hLower hUpper
    (correctedPlusSource Fplus) (correctedMinusSource Fminus)
    hp0 hm0 hcharges.1 hcharges.2

#print axioms actualPlusCharge_orthogonal
#print axioms actualMinusCharge_orthogonal
#print axioms correctedPlusSource_memWeightedL2
#print axioms correctedMinusSource_memWeightedL2
#print axioms actualAffine_corrected_sources_compatible
#print axioms existsUnique_actualInner_affinelyCorrected

end HBL.Profile.ActualInner
