import HBL.WeightedPhaseZeroModeBridge
import HBL.WeightedSourceChargeBridge
import HBL.WeightedSourceFredholmSolution

/-!
# A genuine H-minus regional inverse for sources with two endpoint weights

The original one-layer argument uses 3/2 < sigma < 2.  This lemma establishes
the actual phase-channel inverse first on the stronger source class
L^{2,2}, where the conjugated source Green map coincides with the known
weighted free Green operator.  Extension to the full manuscript range is
not claimed here.

The compatibility condition is the manuscript's physical resonance
pairing, not an abstract Fredholm condition.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedPhaseResonance_data_pairing
    (F : ℝ → ℝ) (hF : InWeightedL2 2 F) :
    inner ℝ weightedPhaseResonanceL2
        (weightedSourceDataL2 2 F hF) =
      channelPairing HartreeChannel.minus F := by
  rw [L2.inner_def]
  unfold channelPairing
  apply integral_congr_ae
  filter_upwards [
      weightedPhaseResonanceL2_ae,
      weightedSourceDataL2_ae 2 F hF] with r hpsi hdata
  rw [hpsi, hdata, Real.inner_apply]
  unfold weightedPhaseResonance channelResonance
  calc
    resonanceMinus r * affineJapaneseDecay 2 r *
        (affineJapaneseWeight 2 r * F r) =
      resonanceMinus r *
        (affineJapaneseDecay 2 r *
          affineJapaneseWeight 2 r) * F r := by ring
    _ = resonanceMinus r * F r := by rw [affineJapaneseDecay_mul_weight, mul_one]

theorem phaseSourceData_charge_zero_iff
    (F : ℝ → ℝ) (hF : InWeightedL2 2 F) :
    inner ℝ (weightedHartreeSineModeL2 1)
        (weightedSourceDataL2 2 F hF) = 0 ↔
      channelPairing HartreeChannel.minus F = 0 := by
  rw [phaseFredholmSource_orthogonal_iff,
    weightedPhaseResonance_data_pairing]

theorem phaseSourceGreen_charge_zero
    (F : ℝ → ℝ) (hF : InWeightedL2 2 F)
    (hcharge : channelPairing HartreeChannel.minus F = 0) :
    inner ℝ (weightedHartreeSineModeL2 1)
        (weightedFreeGreenOperator (weightedSourceDataL2 2 F hF)) = 0 := by
  let d := weightedSourceDataL2 2 F hF
  have hdata : inner ℝ (weightedHartreeSineModeL2 1) d = 0 :=
    (phaseSourceData_charge_zero_iff F hF).2 hcharge
  have hsa := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    weightedFreeGreenOperator_selfAdjoint
  calc
    inner ℝ (weightedHartreeSineModeL2 1) (weightedFreeGreenOperator d) =
        inner ℝ (weightedFreeGreenOperator (weightedHartreeSineModeL2 1)) d :=
      (hsa (weightedHartreeSineModeL2 1) d).symm
    _ = inner ℝ ((1 / 3 : ℝ) • weightedHartreeSineModeL2 1) d := by
      rw [weightedFreeGreenOperator_sineMode 1 (by omega)]
      norm_num
    _ = 0 := by rw [real_inner_smul_left, hdata, mul_zero]

theorem existsUnique_physicalPhaseWeightedSourceSolve
    (F : ℝ → ℝ) (hF : InWeightedL2 2 F)
    (hcharge : channelPairing HartreeChannel.minus F = 0) :
    ∃! x : (1 - weightedPhaseBirman).kerᗮ,
      (1 - weightedPhaseBirman) (x : RealL2 halfLineMeasure) =
        weightedFreeGreenOperator (weightedSourceDataL2 2 F hF) :=
  existsUnique_phaseFredholmSolution
    (weightedFreeGreenOperator (weightedSourceDataL2 2 F hF))
    (phaseSourceGreen_charge_zero F hF hcharge)

#print axioms weightedPhaseResonance_data_pairing
#print axioms phaseSourceData_charge_zero_iff
#print axioms phaseSourceGreen_charge_zero
#print axioms existsUnique_physicalPhaseWeightedSourceSolve

end HBL.Modulation.Monopole
