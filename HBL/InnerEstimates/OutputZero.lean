import HBL.InnerEstimates.NormalizedZero
import HBL.InnerEstimates.RepresentativeZeroSource
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedOutput_zero (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (h0 : InWeightedL2 sigma (fun _ => 0)) :
    normalizedPlusOutput sigma hLower hUpper (fun _ => 0) h0 = (fun _ => 0) ∧
    normalizedMinusOutput sigma hLower hUpper (fun _ => 0) h0 = (fun _ => 0) := by
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
    simp [normalizedPlusOutput, normalizedPlusRemainder, hp, hcp,
      actualPlusCharge, channelPairing, affineRestore, innerGreenRepresentative_zero_source]
  · funext r
    simp [normalizedMinusOutput, normalizedMinusRemainder, hm, hcm,
      actualMinusCharge, channelPairing, affineRestore, innerGreenRepresentative_zero_source]
end HBL.Modulation.Monopole
