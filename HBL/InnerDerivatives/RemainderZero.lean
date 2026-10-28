import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedRemainder_zero (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (h0 : InWeightedL2 sigma (fun _ => 0)) :
    normalizedPlusRemainder sigma hLower hUpper (fun _ => 0) h0 = (fun _ => 0) ∧
    normalizedMinusRemainder sigma hLower hUpper (fun _ => 0) h0 = (fun _ => 0) := by
  have hp := (normalizedInner_zero sigma hLower hUpper h0).1
  have hm := (normalizedInner_zero sigma hLower hUpper h0).2
  have hcp : correctedPlusSource (fun _ => 0) = (fun _ => 0) := by
    funext t
    simp [correctedPlusSource, actualPlusCharge, channelPairing]
  have hcm : correctedMinusSource (fun _ => 0) = (fun _ => 0) := by
    funext t
    simp [correctedMinusSource, actualMinusCharge, channelPairing]
  constructor
  · funext r
    simp [normalizedPlusRemainder, hp, hcp, innerGreenRepresentative_zero_source]
  · funext r
    simp [normalizedMinusRemainder, hm, hcm, innerGreenRepresentative_zero_source]
end HBL.Modulation.Monopole
