import HBL.InnerEstimates.RepresentativeDifferenceIdentity
import HBL.InnerEstimates.GreenBoundNorm
import HBL.InnerEstimates.WeightedNormDifference
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerGreenRepresentative_difference_le
    (g h : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    {r : ℝ} (hr : 0 < r) :
    ‖innerGreenRepresentative g F r - innerGreenRepresentative h G r‖ ≤
      innerGreenMajorantNorm * ‖g - h‖ + innerMomentNorm sigma hsigma *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  rw [innerGreenRepresentative_sub g h sigma (by linarith) F G hF hG r, Real.norm_eq_abs]
  have h := (innerGreenRepresentative_abs_le (g - h) sigma hsigma _
    (innerWeighted_sub_mem sigma F G hF hG) hr).trans
    (innerGreenBound_norm_le (g - h) sigma hsigma _ (innerWeighted_sub_mem sigma F G hF hG))
  rwa [innerWeightedNorm_sub_eq] at h
end HBL.Modulation.Monopole
