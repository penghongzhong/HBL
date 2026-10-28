import HBL.InnerDerivatives.WeightedPotentialNorm
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem inner_second_source_bound (sigma : ℝ) (hsigma : sigma ≤ 2)
    (g : RealL2 halfLineMeasure) (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (Q : ℝ → ℝ) (hQ : Q =ᵐ[halfLineMeasure] (fun r => -(weightedGreenDecay r * g r + F r))) :
    InWeightedL2 sigma Q ∧ innerWeightedNorm sigma Q ≤ ‖g‖ + innerWeightedNorm sigma F := by
  have hp := inner_weighted_potential_norm_le sigma hsigma g
  have hb := innerWeighted_sub_const_mul_bound sigma (fun r => weightedGreenDecay r * g r) F hp.1 hF (-1)
  have hneg : InWeightedL2 sigma (fun r => -(weightedGreenDecay r * g r + F r)) := by
    unfold InWeightedL2
    convert hb.1.neg using 1
    funext r
    simp only [Pi.neg_apply]
    ring
  have hmem : InWeightedL2 sigma Q := by
    apply hneg.ae_eq
    filter_upwards [hQ] with r hr
    rw [hr]
  have he : innerWeightedNorm sigma Q = innerWeightedNorm sigma (fun r => weightedGreenDecay r * g r - (-1) * F r) := by
    unfold innerWeightedNorm
    rw [eLpNorm_congr_ae (show (fun r => affineJapaneseWeight sigma r * Q r) =ᵐ[halfLineMeasure]
      (fun r => -(affineJapaneseWeight sigma r * (weightedGreenDecay r * g r - (-1) * F r))) from by
        filter_upwards [hQ] with r hr
        rw [hr]
        ring)]
    change (eLpNorm (-(fun r => affineJapaneseWeight sigma r * (weightedGreenDecay r * g r - (-1) * F r))) 2 halfLineMeasure).toReal = _
    rw [eLpNorm_neg]
  refine ⟨hmem, ?_⟩
  rw [he]
  have hh := hb.2
  simp only [norm_neg, norm_one, one_mul] at hh
  exact hh.trans (_root_.add_le_add hp.2 le_rfl)
end HBL.Modulation.Monopole
