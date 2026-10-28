import HBL.InnerEstimates.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerFredholm_norm_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K : E →L[ℝ] E) (hK : IsCompactOperator K)
    (x y : (1 - K).kerᗮ) :
    ‖(x : E) - (y : E)‖ ≤ innerFredholmConstant K hK *
      ‖(1 - K) (x : E) - (1 - K) (y : E)‖ := by
  have h := (Classical.choose_spec
    (HBL.Fredholm.one_sub_antilipschitz_on_kernelComplement hK)).le_mul_dist x y
  simpa only [dist_eq_norm, HBL.Fredholm.kernelComplementRestriction,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, innerFredholmConstant,
    ← Submodule.norm_coe, Submodule.coe_sub] using h
end HBL.Modulation.Monopole
