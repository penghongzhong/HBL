import HBL.InnerEstimates.PlusOutputDifference
import HBL.InnerEstimates.OutputZero
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem normalizedPlusOutput_weighted_norm_le
    (sigma tau : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) (htau : 3 / 2 < tau)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    innerWeightedNorm (-tau) (normalizedPlusOutput sigma hLower hUpper F hF) ≤
      innerPlusOutputConstant sigma tau hLower hUpper htau * innerWeightedNorm sigma F := by
  have h0 : InWeightedL2 sigma (fun _ => 0) := by simp [InWeightedL2]
  have h := normalizedPlusOutput_weighted_difference_le sigma tau hLower hUpper htau F (fun _ => 0) hF h0
  rw [(normalizedOutput_zero sigma hLower hUpper h0).1, innerWeightedData_zero] at h
  simpa only [sub_zero, ← innerWeightedNorm_eq] using h
end HBL.Modulation.Monopole
