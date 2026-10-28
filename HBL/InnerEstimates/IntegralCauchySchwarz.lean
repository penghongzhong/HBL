import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_integral_norm_mul_le (f g : ℝ → ℝ)
    (hf : MemLp f 2 halfLineMeasure) (hg : MemLp g 2 halfLineMeasure) :
    (∫ r, ‖f r * g r‖ ∂halfLineMeasure) ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have hi : (∫ r, ‖f r * g r‖ ∂halfLineMeasure) =
      inner ℝ (hf.norm.toLp (fun r => ‖f r‖)) (hg.norm.toLp (fun r => ‖g r‖)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.norm.coeFn_toLp, hg.norm.coeFn_toLp] with r hf' hg'
    rw [hf', hg', Real.inner_apply, norm_mul]
  rw [hi]
  simpa only [Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable,
    eLpNorm_norm g hg.aestronglyMeasurable] using
    (real_inner_le_norm (hf.norm.toLp (fun r => ‖f r‖))
      (hg.norm.toLp (fun r => ‖g r‖)))
end HBL.Modulation.Monopole
