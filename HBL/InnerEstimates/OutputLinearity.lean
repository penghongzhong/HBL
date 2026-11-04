import HBL.InnerEstimates.FredholmDifference
import HBL.InnerEstimates.PlusEquation
import HBL.InnerEstimates.MinusEquation
import HBL.InnerEstimates.RepresentativeDifferenceIdentity

/-!
Linearity of the actual normalized, affine-restored inner solvers.  The
affine charges, the fixed Fredholm solutions, and their Green representatives
are all the ones already used by the physical inner reconstruction.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeighted_add_smul_mem (sigma : ℝ) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ) :
    InWeightedL2 sigma (fun r => F r + a * G r) := by
  unfold InWeightedL2 at *
  convert hF.add (hG.const_mul a) using 1
  funext r
  simp only [Pi.add_apply]
  ring

theorem weightedSourceDataL2_add_smul
    (sigma : ℝ) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r + a * G r)) :
    weightedSourceDataL2 sigma (fun r => F r + a * G r) hH =
      weightedSourceDataL2 sigma F hF + a • weightedSourceDataL2 sigma G hG := by
  apply Lp.ext
  filter_upwards [weightedSourceDataL2_ae sigma _ hH,
    Lp.coeFn_add (weightedSourceDataL2 sigma F hF)
      (a • weightedSourceDataL2 sigma G hG),
    Lp.coeFn_smul a (weightedSourceDataL2 sigma G hG),
    weightedSourceDataL2_ae sigma F hF,
    weightedSourceDataL2_ae sigma G hG] with r hH' hadd hsmul hF' hG'
  rw [hH', hadd]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hF', hG']
  ring

private theorem actualPlusCharge_add_smul
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ) :
    actualPlusCharge (fun r => F r + a * G r) =
      actualPlusCharge F + a * actualPlusCharge G := by
  have hH := innerWeighted_add_smul_mem sigma F G hF hG a
  have hpair : channelPairing HartreeChannel.plus (fun r => F r + a * G r) =
      channelPairing HartreeChannel.plus F +
        a * channelPairing HartreeChannel.plus G := by
    rw [← weightedSourceResonance_inner_data_eq_pairing sigma hsigma _ hH,
      weightedSourceDataL2_add_smul sigma F G hF hG a hH,
      inner_add_right, real_inner_smul_right,
      weightedSourceResonance_inner_data_eq_pairing,
      weightedSourceResonance_inner_data_eq_pairing]
  simp only [actualPlusCharge_eq_twice_pairing, hpair]
  ring

private theorem actualMinusCharge_add_smul
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ) :
    actualMinusCharge (fun r => F r + a * G r) =
      actualMinusCharge F + a * actualMinusCharge G := by
  have hH := innerWeighted_add_smul_mem sigma F G hF hG a
  have hpair : channelPairing HartreeChannel.minus (fun r => F r + a * G r) =
      channelPairing HartreeChannel.minus F +
        a * channelPairing HartreeChannel.minus G := by
    rw [← weightedPhaseSourceResonance_inner_data_eq_pairing sigma hsigma _ hH,
      weightedSourceDataL2_add_smul sigma F G hF hG a hH,
      inner_add_right, real_inner_smul_right,
      weightedPhaseSourceResonance_inner_data_eq_pairing,
      weightedPhaseSourceResonance_inner_data_eq_pairing]
  simp only [actualMinusCharge_eq_neg_pairing, hpair]
  ring

private theorem correctedPlusDataL2_add_smul
    (sigma : ℝ) (hLower : 1 / 2 < sigma) (hUpper : sigma ≤ 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r + a * G r)) :
    correctedPlusDataL2 sigma hUpper (fun r => F r + a * G r) hH =
      correctedPlusDataL2 sigma hUpper F hF +
        a • correctedPlusDataL2 sigma hUpper G hG := by
  rw [correctedPlusDataL2_eq, correctedPlusDataL2_eq, correctedPlusDataL2_eq,
    weightedSourceDataL2_add_smul sigma F G hF hG a hH,
    actualPlusCharge_add_smul sigma hLower F G hF hG a]
  simp only [add_smul, mul_smul, smul_sub]
  abel

private theorem correctedMinusDataL2_add_smul
    (sigma : ℝ) (hLower : 1 / 2 < sigma) (hUpper : sigma ≤ 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r + a * G r)) :
    correctedMinusDataL2 sigma hUpper (fun r => F r + a * G r) hH =
      correctedMinusDataL2 sigma hUpper F hF +
        a • correctedMinusDataL2 sigma hUpper G hG := by
  rw [correctedMinusDataL2_eq, correctedMinusDataL2_eq, correctedMinusDataL2_eq,
    weightedSourceDataL2_add_smul sigma F G hF hG a hH,
    actualMinusCharge_add_smul sigma hLower F G hF hG a]
  simp only [add_smul, mul_smul, smul_sub]
  abel

private theorem normalizedPlusInner_add_smul
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r + a * G r)) :
    (normalizedPlusInner sigma hLower hUpper (fun r => F r + a * G r) hH :
        RealL2 halfLineMeasure) =
      (normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) +
        a • (normalizedPlusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure) := by
  have h := innerFredholm_norm_sub_le weightedBirmanSchwingerOperator
    weightedBirmanSchwingerOperator_compact
    (normalizedPlusInner sigma hLower hUpper (fun r => F r + a * G r) hH)
    (normalizedPlusInner sigma hLower hUpper F hF +
      a • normalizedPlusInner sigma hLower hUpper G hG)
  simp only [Submodule.coe_add, Submodule.coe_smul] at h
  have heq :
      (1 - weightedBirmanSchwingerOperator)
          (normalizedPlusInner sigma hLower hUpper (fun r => F r + a * G r) hH :
            RealL2 halfLineMeasure) =
        (1 - weightedBirmanSchwingerOperator)
          ((normalizedPlusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) +
            a • (normalizedPlusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure)) := by
    rw [map_add, map_smul, normalizedPlusInner_equation, normalizedPlusInner_equation,
      normalizedPlusInner_equation,
      correctedPlusDataL2_add_smul sigma (by linarith) hUpper.le F G hF hG a hH,
      map_add, map_smul]
  rw [heq, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

private theorem normalizedMinusInner_add_smul
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r + a * G r)) :
    (normalizedMinusInner sigma hLower hUpper (fun r => F r + a * G r) hH :
        RealL2 halfLineMeasure) =
      (normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) +
        a • (normalizedMinusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure) := by
  have h := innerFredholm_norm_sub_le weightedPhaseBirman weightedPhaseBirman_compact
    (normalizedMinusInner sigma hLower hUpper (fun r => F r + a * G r) hH)
    (normalizedMinusInner sigma hLower hUpper F hF +
      a • normalizedMinusInner sigma hLower hUpper G hG)
  simp only [Submodule.coe_add, Submodule.coe_smul] at h
  have heq :
      (1 - weightedPhaseBirman)
          (normalizedMinusInner sigma hLower hUpper (fun r => F r + a * G r) hH :
            RealL2 halfLineMeasure) =
        (1 - weightedPhaseBirman)
          ((normalizedMinusInner sigma hLower hUpper F hF : RealL2 halfLineMeasure) +
            a • (normalizedMinusInner sigma hLower hUpper G hG : RealL2 halfLineMeasure)) := by
    rw [map_add, map_smul, normalizedMinusInner_equation, normalizedMinusInner_equation,
      normalizedMinusInner_equation,
      correctedMinusDataL2_add_smul sigma (by linarith) hUpper.le F G hF hG a hH,
      map_add, map_smul]
  rw [heq, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

private theorem innerGreenRepresentative_add_smul
    (g h : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    (a r : ℝ) :
    innerGreenRepresentative (g + a • h) (fun rho => F rho + a * G rho) r =
      innerGreenRepresentative g F r + a * innerGreenRepresentative h G r := by
  have hprim : weightedGreenPrimitive (g + a • h) r =
      weightedGreenPrimitive g r + a * weightedGreenPrimitive h r := by
    unfold weightedGreenPrimitive
    rw [← integral_const_mul,
      ← integral_add (weightedGreenPrimitive_integrable_kernel g r)
        ((weightedGreenPrimitive_integrable_kernel h r).const_mul a)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add g (a • h), Lp.coeFn_smul a h] with rho hadd hsmul
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsource : halfLineMinGreen (fun rho => F rho + a * G rho) r =
      halfLineMinGreen F r + a * halfLineMinGreen G r := by
    unfold halfLineMinGreen
    rw [← integral_const_mul,
      ← integral_add
        (halfLineMinGreen_kernel_integrable F (weightedSource_integrable sigma hsigma F hF) r)
        ((halfLineMinGreen_kernel_integrable G
          (weightedSource_integrable sigma hsigma G hG) r).const_mul a)]
    apply integral_congr_ae
    filter_upwards with rho
    ring
  unfold innerGreenRepresentative
  rw [hprim, hsource]
  ring

/-- The fixed normalized H-plus inverse, with its forced affine slope restored,
is linear on the genuine weighted source space. -/
theorem normalizedPlusOutput_add_smul
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r + a * G r)) :
    normalizedPlusOutput sigma hLower hUpper (fun r => F r + a * G r) hH =
      fun r => normalizedPlusOutput sigma hLower hUpper F hF r +
        a * normalizedPlusOutput sigma hLower hUpper G hG r := by
  have hcharge := actualPlusCharge_add_smul sigma (by linarith) F G hF hG a
  have hsource : correctedPlusSource (fun r => F r + a * G r) =
      fun r => correctedPlusSource F r + a * correctedPlusSource G r := by
    funext r
    unfold correctedPlusSource
    rw [hcharge]
    ring
  funext r
  unfold normalizedPlusOutput affineRestore normalizedPlusRemainder
  rw [normalizedPlusInner_add_smul sigma hLower hUpper F G hF hG a hH,
    map_add, map_smul, hsource,
    innerGreenRepresentative_add_smul _ _ sigma (by linarith) _ _
      (correctedPlusSource_memWeightedL2 sigma hUpper.le F hF)
      (correctedPlusSource_memWeightedL2 sigma hUpper.le G hG) a r,
    hcharge]
  ring

/-- The fixed normalized H-minus inverse obeys the same exact linearity;
the physical phase charge is recomputed from the source. -/
theorem normalizedMinusOutput_add_smul
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) (a : ℝ)
    (hH : InWeightedL2 sigma (fun r => F r + a * G r)) :
    normalizedMinusOutput sigma hLower hUpper (fun r => F r + a * G r) hH =
      fun r => normalizedMinusOutput sigma hLower hUpper F hF r +
        a * normalizedMinusOutput sigma hLower hUpper G hG r := by
  have hcharge := actualMinusCharge_add_smul sigma (by linarith) F G hF hG a
  have hsource : correctedMinusSource (fun r => F r + a * G r) =
      fun r => correctedMinusSource F r + a * correctedMinusSource G r := by
    funext r
    unfold correctedMinusSource
    rw [hcharge]
    ring
  funext r
  unfold normalizedMinusOutput affineRestore normalizedMinusRemainder
  rw [normalizedMinusInner_add_smul sigma hLower hUpper F G hF hG a hH,
    smul_add, smul_comm (3 : ℝ) a, hsource,
    innerGreenRepresentative_add_smul _ _ sigma (by linarith) _ _
      (correctedMinusSource_memWeightedL2 sigma hUpper.le F hF)
      (correctedMinusSource_memWeightedL2 sigma hUpper.le G hG) a r,
    hcharge]
  ring

end HBL.Modulation.Monopole
