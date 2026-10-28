import HBL.WeightedSourceGreen
import HBL.WeightedScaleResonance

/-!
# Weighted-source charge pairing

This file identifies the manuscript threshold pairing on
L^{2,sigma}(0,infinity) with an ordinary half-line L2 inner product after
multiplying the datum by the Japanese-bracket weight.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem weightedSourceData_memLp_two
    (sigma : ℝ) (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    MemLp (fun r => affineJapaneseWeight sigma r * F r) 2
      halfLineMeasure := by
  exact hF

def weightedSourceDataL2
    (sigma : ℝ) (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    RealL2 halfLineMeasure :=
  (weightedSourceData_memLp_two sigma F hF).toLp
    (fun r => affineJapaneseWeight sigma r * F r)

theorem weightedSourceDataL2_ae
    (sigma : ℝ) (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    (weightedSourceDataL2 sigma F hF : ℝ → ℝ) =ᵐ[halfLineMeasure]
      fun r => affineJapaneseWeight sigma r * F r :=
  (weightedSourceData_memLp_two sigma F hF).coeFn_toLp

def weightedSourceResonance (sigma : ℝ) (r : ℝ) : ℝ :=
  resonancePlus r * affineJapaneseDecay sigma r

theorem weightedSourceResonance_memLp_two
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    MemLp (weightedSourceResonance sigma) 2 halfLineMeasure := by
  simpa only [weightedSourceResonance, channelResonance] using
    channelResonance_decay_memLp_two HartreeChannel.plus sigma hsigma

def weightedSourceResonanceL2
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    RealL2 halfLineMeasure :=
  (weightedSourceResonance_memLp_two sigma hsigma).toLp
    (weightedSourceResonance sigma)

theorem weightedSourceResonanceL2_ae
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    (weightedSourceResonanceL2 sigma hsigma : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedSourceResonance sigma :=
  (weightedSourceResonance_memLp_two sigma hsigma).coeFn_toLp

theorem weightedSourceResonance_inner_data_eq_pairing
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    inner ℝ (weightedSourceResonanceL2 sigma hsigma)
        (weightedSourceDataL2 sigma F hF) =
      channelPairing HartreeChannel.plus F := by
  rw [L2.inner_def]
  unfold channelPairing
  apply integral_congr_ae
  filter_upwards [
      weightedSourceResonanceL2_ae sigma hsigma,
      weightedSourceDataL2_ae sigma F hF] with r hpsi hdata
  rw [hpsi, hdata, Real.inner_apply]
  unfold weightedSourceResonance channelResonance
  rw [show
      (resonancePlus r * affineJapaneseDecay sigma r) *
          (affineJapaneseWeight sigma r * F r) =
        resonancePlus r *
          (affineJapaneseDecay sigma r *
            affineJapaneseWeight sigma r) * F r by ring,
    affineJapaneseDecay_mul_weight, mul_one]

theorem weightedSourceResonance_inner_data_zero_iff
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    inner ℝ (weightedSourceResonanceL2 sigma hsigma)
        (weightedSourceDataL2 sigma F hF) = 0 ↔
      channelPairing HartreeChannel.plus F = 0 := by
  rw [weightedSourceResonance_inner_data_eq_pairing]

#print axioms weightedSourceResonance_inner_data_eq_pairing
#print axioms weightedSourceResonance_inner_data_zero_iff

end HBL.Modulation.Monopole
