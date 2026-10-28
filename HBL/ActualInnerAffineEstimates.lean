import HBL.ActualInnerAffinelyCorrected

/-!
# Quantitative stability of the actual affine charge subtraction

The constants are the norms of the physical weighted resonances and affine
sources. They are independent of the two input sources. This supplies
weighted source estimates, not a classical reconstruction or a Kummer bound.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Profile.ActualInner

open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Modulation.Monopole

theorem actualPlusCharge_eq_twice_pairing (F : ℝ → ℝ) :
    actualPlusCharge F = 2 * channelPairing HartreeChannel.plus F := by
  simp [actualPlusCharge, channelLimit, div_neg, mul_comm]

theorem actualMinusCharge_eq_neg_pairing (F : ℝ → ℝ) :
    actualMinusCharge F = -channelPairing HartreeChannel.minus F := by
  simp [actualMinusCharge, channelLimit]

theorem actualPlusCharge_difference_le
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    ‖actualPlusCharge F - actualPlusCharge G‖ ≤
      (2 * ‖weightedSourceResonanceL2 sigma hsigma‖) *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have heq : actualPlusCharge F - actualPlusCharge G =
      2 * inner ℝ (weightedSourceResonanceL2 sigma hsigma)
        (weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG) := by
    rw [inner_sub_right, weightedSourceResonance_inner_data_eq_pairing,
      weightedSourceResonance_inner_data_eq_pairing,
      actualPlusCharge_eq_twice_pairing, actualPlusCharge_eq_twice_pairing]
    ring
  rw [heq, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (‖weightedSourceResonanceL2 sigma hsigma‖ *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ = _ := by ring

theorem actualMinusCharge_difference_le
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    ‖actualMinusCharge F - actualMinusCharge G‖ ≤
      ‖weightedPhaseSourceResonanceL2 sigma hsigma‖ *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have heq : actualMinusCharge F - actualMinusCharge G =
      -inner ℝ (weightedPhaseSourceResonanceL2 sigma hsigma)
        (weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG) := by
    rw [inner_sub_right, weightedPhaseSourceResonance_inner_data_eq_pairing,
      weightedPhaseSourceResonance_inner_data_eq_pairing,
      actualMinusCharge_eq_neg_pairing, actualMinusCharge_eq_neg_pairing]
    ring
  rw [heq, norm_neg]
  exact norm_inner_le_norm _ _

theorem weightedSourceDataL2_sub_const_mul
    (sigma : ℝ) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r - a * G r)) :
    weightedSourceDataL2 sigma (fun r => F r - a * G r) hH =
      weightedSourceDataL2 sigma F hF - a • weightedSourceDataL2 sigma G hG := by
  apply Lp.ext
  filter_upwards [weightedSourceDataL2_ae sigma _ hH,
    Lp.coeFn_sub (weightedSourceDataL2 sigma F hF)
      (a • weightedSourceDataL2 sigma G hG),
    Lp.coeFn_smul a (weightedSourceDataL2 sigma G hG),
    weightedSourceDataL2_ae sigma F hF,
    weightedSourceDataL2_ae sigma G hG] with r hH' hsub hsmul hF' hG'
  rw [hH', hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hF', hG']
  ring

def plusAffineSourceDataL2 (sigma : ℝ) (hUpper : sigma ≤ 2) :
    RealL2 halfLineMeasure :=
  weightedSourceDataL2 sigma (channelAffineSource HartreeChannel.plus)
    (hPlusAffineSource_inWeightedL2 sigma hUpper)

def minusAffineSourceDataL2 (sigma : ℝ) (hUpper : sigma ≤ 2) :
    RealL2 halfLineMeasure :=
  weightedSourceDataL2 sigma (channelAffineSource HartreeChannel.minus)
    (phaseAffineSource_inWeightedL2 sigma hUpper)

def correctedPlusDataL2 (sigma : ℝ) (hUpper : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : RealL2 halfLineMeasure :=
  weightedSourceDataL2 sigma (correctedPlusSource F)
    (correctedPlusSource_memWeightedL2 sigma hUpper F hF)

def correctedMinusDataL2 (sigma : ℝ) (hUpper : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) : RealL2 halfLineMeasure :=
  weightedSourceDataL2 sigma (correctedMinusSource F)
    (correctedMinusSource_memWeightedL2 sigma hUpper F hF)

theorem correctedPlusDataL2_eq
    (sigma : ℝ) (hUpper : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    correctedPlusDataL2 sigma hUpper F hF =
      weightedSourceDataL2 sigma F hF -
        actualPlusCharge F • plusAffineSourceDataL2 sigma hUpper := by
  exact weightedSourceDataL2_sub_const_mul sigma F
    (channelAffineSource HartreeChannel.plus) hF
    (hPlusAffineSource_inWeightedL2 sigma hUpper) (actualPlusCharge F)
    (correctedPlusSource_memWeightedL2 sigma hUpper F hF)

theorem correctedMinusDataL2_eq
    (sigma : ℝ) (hUpper : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    correctedMinusDataL2 sigma hUpper F hF =
      weightedSourceDataL2 sigma F hF -
        actualMinusCharge F • minusAffineSourceDataL2 sigma hUpper := by
  exact weightedSourceDataL2_sub_const_mul sigma F
    (channelAffineSource HartreeChannel.minus) hF
    (phaseAffineSource_inWeightedL2 sigma hUpper) (actualMinusCharge F)
    (correctedMinusSource_memWeightedL2 sigma hUpper F hF)

theorem correctedPlusDataL2_difference_le
    (sigma : ℝ) (hLower : 1 / 2 < sigma) (hUpper : sigma ≤ 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    ‖correctedPlusDataL2 sigma hUpper F hF - correctedPlusDataL2 sigma hUpper G hG‖ ≤
      (1 + 2 * ‖weightedSourceResonanceL2 sigma hLower‖ *
        ‖plusAffineSourceDataL2 sigma hUpper‖) *
      ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  rw [correctedPlusDataL2_eq, correctedPlusDataL2_eq]
  have heq :
      (weightedSourceDataL2 sigma F hF - actualPlusCharge F •
          plusAffineSourceDataL2 sigma hUpper) -
        (weightedSourceDataL2 sigma G hG - actualPlusCharge G •
          plusAffineSourceDataL2 sigma hUpper) =
      (weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG) -
        (actualPlusCharge F - actualPlusCharge G) •
          plusAffineSourceDataL2 sigma hUpper := by rw [sub_smul]; abel
  rw [heq]
  calc
    _ ≤ ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ +
        ‖(actualPlusCharge F - actualPlusCharge G) •
          plusAffineSourceDataL2 sigma hUpper‖ := norm_sub_le _ _
    _ = ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ +
        ‖actualPlusCharge F - actualPlusCharge G‖ *
          ‖plusAffineSourceDataL2 sigma hUpper‖ := by rw [norm_smul]
    _ ≤ ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ +
        ((2 * ‖weightedSourceResonanceL2 sigma hLower‖) *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) *
          ‖plusAffineSourceDataL2 sigma hUpper‖ := by
      exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (actualPlusCharge_difference_le sigma hLower F G hF hG)
        (norm_nonneg (plusAffineSourceDataL2 sigma hUpper)))
    _ = _ := by ring

theorem correctedMinusDataL2_difference_le
    (sigma : ℝ) (hLower : 1 / 2 < sigma) (hUpper : sigma ≤ 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) :
    ‖correctedMinusDataL2 sigma hUpper F hF - correctedMinusDataL2 sigma hUpper G hG‖ ≤
      (1 + ‖weightedPhaseSourceResonanceL2 sigma hLower‖ *
        ‖minusAffineSourceDataL2 sigma hUpper‖) *
      ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  rw [correctedMinusDataL2_eq, correctedMinusDataL2_eq]
  have heq :
      (weightedSourceDataL2 sigma F hF - actualMinusCharge F •
          minusAffineSourceDataL2 sigma hUpper) -
        (weightedSourceDataL2 sigma G hG - actualMinusCharge G •
          minusAffineSourceDataL2 sigma hUpper) =
      (weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG) -
        (actualMinusCharge F - actualMinusCharge G) •
          minusAffineSourceDataL2 sigma hUpper := by rw [sub_smul]; abel
  rw [heq]
  calc
    _ ≤ ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ +
        ‖(actualMinusCharge F - actualMinusCharge G) •
          minusAffineSourceDataL2 sigma hUpper‖ := norm_sub_le _ _
    _ = ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ +
        ‖actualMinusCharge F - actualMinusCharge G‖ *
          ‖minusAffineSourceDataL2 sigma hUpper‖ := by rw [norm_smul]
    _ ≤ ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ +
        (‖weightedPhaseSourceResonanceL2 sigma hLower‖ *
          ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖) *
          ‖minusAffineSourceDataL2 sigma hUpper‖ := by
      exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (actualMinusCharge_difference_le sigma hLower F G hF hG)
        (norm_nonneg (minusAffineSourceDataL2 sigma hUpper)))
    _ = _ := by ring

end HBL.Profile.ActualInner
