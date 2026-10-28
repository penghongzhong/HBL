import HBL.InnerReconstruction.AffineModelWeightedOutput
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem affineRestore_properties (q : ℝ → ℝ) (a : ℝ) (hq : InnerRemainderProperties q) :
    InnerAffineProperties (affineRestore q a) a := by
  rcases hq with ⟨hc, hzero, hw, d, hd⟩
  refine ⟨hc.add (model_contDiff_infty.continuous.const_mul a), ?_, ?_, d, ?_⟩
  · simp [affineRestore, hzero, model_zero]
  · intro tau htau
    have h := (hw tau (by linarith)).add ((affineModel_inWeightedL2_neg tau htau).const_mul a)
    unfold InWeightedL2
    convert h using 1
    funext r
    simp only [Pi.add_apply]
    unfold affineRestore
    ring
  · apply hd.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    simp [affineRestore, model_eq_id_of_two_le r hr]
end HBL.Modulation.Monopole
