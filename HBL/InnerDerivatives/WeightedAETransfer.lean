import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem innerWeighted_ae_transfer (sigma : ℝ) (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hFG : F =ᵐ[halfLineMeasure] G) :
    InWeightedL2 sigma G ∧ innerWeightedNorm sigma G = innerWeightedNorm sigma F := by
  have he : (fun r => affineJapaneseWeight sigma r * F r) =ᵐ[halfLineMeasure]
      (fun r => affineJapaneseWeight sigma r * G r) := by
    filter_upwards [hFG] with r hr
    rw [hr]
  exact ⟨hF.ae_eq he, congrArg ENNReal.toReal (eLpNorm_congr_ae he.symm)⟩
end HBL.Modulation.Monopole
