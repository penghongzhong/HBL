import HBL.InnerDerivatives.GreenDerivativeBound
import HBL.InnerEstimates.WeightedNormDifference
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerGreenDerivative_difference_le (g h : RealL2 halfLineMeasure)
    (sigma : ℝ) (hsigma : 3 / 2 < sigma) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G) {r : ℝ} (hr : 0 < r) :
    (1 + r) * ‖innerGreenDerivative g F r - innerGreenDerivative h G r‖ ≤
      innerGreenDerivativeMajorant * ‖g - h‖ + innerSourceDerivativeMajorant sigma hsigma *
        ‖weightedSourceDataL2 sigma F hF - weightedSourceDataL2 sigma G hG‖ := by
  have hfg := innerWeighted_sub_mem sigma F G hF hG
  have hbound := innerGreenDerivative_bound (g - h) sigma hsigma (fun r => F r - G r) hfg hr
  rw [innerWeightedNorm_sub_eq sigma F G hF hG] at hbound
  have hsub : innerGreenDerivative g F r - innerGreenDerivative h G r =
      innerGreenDerivative (g - h) (fun t => F t - G t) r := by
    have hi := (inner_totalSource_integral_norm_le g sigma hsigma F hF).1.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hr.le) le_rfl)
    have hj := (inner_totalSource_integral_norm_le h sigma hsigma G hG).1.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hr.le) le_rfl)
    unfold innerGreenDerivative halfLineGreenTail
    rw [← integral_sub hi hj]
    apply integral_congr_ae
    have hae := (Lp.coeFn_sub g h).filter_mono (ae_mono (Measure.restrict_mono (Ioi_subset_Ioi hr.le) le_rfl))
    filter_upwards [hae] with t ht
    rw [ht]
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  exact hbound
end HBL.Modulation.Monopole
