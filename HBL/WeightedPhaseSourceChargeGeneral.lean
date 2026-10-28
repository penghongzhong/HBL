import HBL.WeightedPhaseZeroModeBridge
import HBL.WeightedSourceChargeBridge

/-!
# Physical H-minus threshold charge on the full manuscript weighted range

The actual phase resonance psi_minus(r)=r/sqrt(1+r^2) defines a bounded
functional on physical L^{2,sigma}(0,infinity) whenever sigma>1/2.
After conjugating the physical datum by <r>^sigma, the exact pairing
is the ordinary Hilbert inner product with psi_minus <r>^(-sigma).
In particular this covers the original 3/2<sigma<2 range without
assuming extra endpoint weights.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

def weightedPhaseSourceResonance (sigma : ℝ) (r : ℝ) : ℝ :=
  resonanceMinus r * affineJapaneseDecay sigma r

theorem weightedPhaseSourceResonance_memLp_two
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    MemLp (weightedPhaseSourceResonance sigma) 2 halfLineMeasure := by
  change MemLp
    (fun r : ℝ => resonanceMinus r * affineJapaneseDecay sigma r)
    2 halfLineMeasure
  exact channelResonance_decay_memLp_two HartreeChannel.minus sigma hsigma

def weightedPhaseSourceResonanceL2
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) : RealL2 halfLineMeasure :=
  (weightedPhaseSourceResonance_memLp_two sigma hsigma).toLp
    (weightedPhaseSourceResonance sigma)

theorem weightedPhaseSourceResonanceL2_ae
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    (weightedPhaseSourceResonanceL2 sigma hsigma : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedPhaseSourceResonance sigma :=
  (weightedPhaseSourceResonance_memLp_two sigma hsigma).coeFn_toLp

theorem weightedPhaseSourceResonance_inner_data_eq_pairing
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    inner ℝ (weightedPhaseSourceResonanceL2 sigma hsigma)
        (weightedSourceDataL2 sigma F hF) =
      channelPairing HartreeChannel.minus F := by
  rw [L2.inner_def]
  unfold channelPairing
  apply integral_congr_ae
  filter_upwards [
    weightedPhaseSourceResonanceL2_ae sigma hsigma,
    weightedSourceDataL2_ae sigma F hF] with r hpsi hdata
  rw [hpsi, hdata, Real.inner_apply]
  unfold weightedPhaseSourceResonance channelResonance
  calc
    resonanceMinus r * affineJapaneseDecay sigma r *
        (affineJapaneseWeight sigma r * F r) =
      resonanceMinus r *
        (affineJapaneseDecay sigma r *
          affineJapaneseWeight sigma r) * F r := by ring
    _ = resonanceMinus r * F r := by
      rw [affineJapaneseDecay_mul_weight, mul_one]

theorem weightedPhaseSourceResonance_inner_data_zero_iff
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    inner ℝ (weightedPhaseSourceResonanceL2 sigma hsigma)
        (weightedSourceDataL2 sigma F hF) = 0 ↔
      channelPairing HartreeChannel.minus F = 0 := by
  rw [weightedPhaseSourceResonance_inner_data_eq_pairing]

#print axioms weightedPhaseSourceResonance_memLp_two
#print axioms weightedPhaseSourceResonance_inner_data_eq_pairing
#print axioms weightedPhaseSourceResonance_inner_data_zero_iff

end HBL.Modulation.Monopole
