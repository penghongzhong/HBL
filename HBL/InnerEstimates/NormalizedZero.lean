import HBL.InnerEstimates.PlusHilbertDifference
import HBL.InnerEstimates.MinusHilbertDifference
import HBL.InnerEstimates.ZeroData
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedInner_zero (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (h0 : InWeightedL2 sigma (fun _ => 0)) :
    normalizedPlusInner sigma hLower hUpper (fun _ => 0) h0 = 0 ∧
    normalizedMinusInner sigma hLower hUpper (fun _ => 0) h0 = 0 := by
  constructor
  · have hc : correctedPlusDataL2 sigma hUpper.le (fun _ => 0) h0 = 0 := by
      rw [correctedPlusDataL2_eq, innerWeightedData_zero]
      simp [actualPlusCharge, channelPairing]
    have h := innerFredholm_norm_sub_le weightedBirmanSchwingerOperator
      weightedBirmanSchwingerOperator_compact
      (normalizedPlusInner sigma hLower hUpper (fun _ => 0) h0) 0
    apply Subtype.ext
    apply norm_le_zero_iff.mp
    rw [normalizedPlusInner_equation, hc, map_zero] at h
    simpa only [ZeroMemClass.coe_zero, map_zero, sub_zero, norm_zero, mul_zero] using h
  · have hc : correctedMinusDataL2 sigma hUpper.le (fun _ => 0) h0 = 0 := by
      rw [correctedMinusDataL2_eq, innerWeightedData_zero]
      simp [actualMinusCharge, channelPairing]
    have h := innerFredholm_norm_sub_le weightedPhaseBirman weightedPhaseBirman_compact
      (normalizedMinusInner sigma hLower hUpper (fun _ => 0) h0) 0
    apply Subtype.ext
    apply norm_le_zero_iff.mp
    rw [normalizedMinusInner_equation, hc, map_zero] at h
    simpa only [ZeroMemClass.coe_zero, map_zero, sub_zero, norm_zero, mul_zero] using h
end HBL.Modulation.Monopole
