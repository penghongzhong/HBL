import HBL.ActualInnerAffinelyCorrected
import HBL.KummerOriginGreen.GreenTerminal
import HBL.RemotePerturbationInverse
import Mathlib.Tactic

/-!
# One-layer physical regional solver bridge, independent of abstract packages

The actual Hartree H_plus and H_minus channels are represented by their
fixed physical weighted Birman--Schwinger kernels and uniquely forced
affine resonance charges; the Kummer channel is the TRUE origin-gauge
two-ended Green integral on a prescribed positive annulus, uniformly for
compact modulation parameter sets.

The remote perturbation inverse is already separately constructed under
the displayed smallness and explicit free-block assumptions in
RemotePerturbationInverse. This joint bridge does not promote an arbitrary
RegionalSolver/ThresholdSolver to a physical PDE solver. The actual
low-weight source identification, moving overlap and full generated-term
classification remain *unproved* for original prop:one-layer-stage3.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace HBL.Profile.OneLayerPhysical
open HBL.Profile.ActualInner
open HBL.Profile.Kummer
open HBL.Modulation.Monopole
open HBL.Modulation.AffineTail
open HBL.L2Kernel

/-- Actual simultaneous normalized Hartree inner corrections, two unique
affine charges, and origin-normalized Kummer correction for every continuous
physical annulus forcing, with uniform C¹ control on compact parameter sets.
No abstract regional solver is a hypothesis. -/
theorem actual_Hartree_inner_Kummer_regional_bridge
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (Fplus Fminus : ℝ → ℝ)
    (hp : InWeightedL2 sigma Fplus)
    (hm : InWeightedL2 sigma Fminus)
    (A : Set (ℝ × ℝ)) (hA : IsCompact A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∃! charges : ℝ × ℝ,
        AffineTailOrthogonal HartreeChannel.plus Fplus charges.1 ∧
        AffineTailOrthogonal HartreeChannel.minus Fminus charges.2) ∧
    (∃! x : InnerCorrections,
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
            (correctedMinusSource_memWeightedL2 sigma hUpper.le Fminus hm))) ∧
    (∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ p ∈ A, ∃ K : OriginKummerPair p.1 p.2 (b + 1),
        OriginBasisOn K a b C ∧ OriginBasisNormalization K ∧
        (∀ (F : ℝ → ℂ), Continuous F →
          (∀ r ∈ Ioo a b,
            HasDerivAt (originGreenValue K a b F)
              (originGreenSlope K a b F r) r ∧
            HasDerivAt (originGreenSlope K a b F)
              (originGreenSecond K a b F r) r ∧
            originGreenSecond K a b F r +
              frozenFirstCoeff r * originGreenSlope K a b F r +
              frozenZeroCoeff p.1 p.2 * originGreenValue K a b F r = F r) ∧
          (originGreenValue K a b F b * originPhysicalSlope K.x K.dx b -
            originGreenSlope K a b F b * originPhysicalValue K.x b = 0) ∧
          (originPhysicalValue K.y a * originGreenSlope K a b F a -
            originPhysicalSlope K.y K.dy a * originGreenValue K a b F a = 0) ∧
          (∀ M : ℝ, 0 ≤ M →
            (∀ r ∈ Icc a b, ‖F r‖ ≤ M) →
              ∀ r ∈ Icc a b,
                ‖originGreenValue K a b F r‖ +
                  ‖originGreenSlope K a b F r‖ ≤
                    (2 * C ^ 3 * (b - a)) * M))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact existsUnique_actual_twoChannel_affine_charges
      sigma hLower hUpper Fplus Fminus hp hm
  · exact existsUnique_actualInner_affinelyCorrected
      sigma hLower hUpper Fplus Fminus hp hm
  · exact exists_compact_originGreen_outgoing_and_uniform A hA a b ha hab

end HBL.Profile.OneLayerPhysical
