import HBL.InnerEstimates.BoundedWeightedNorm
import HBL.InnerEstimates.WeightedAffineNorm
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem affineRestore_weighted_difference_bound (tau : ℝ) (htau : 3 / 2 < tau)
    (q s : ℝ → ℝ) (hq : Continuous q) (hs : Continuous s) (a b C : ℝ)
    (hC : ∀ r : ℝ, 0 < r → ‖q r - s r‖ ≤ C) :
    InWeightedL2 (-tau) (fun r => affineRestore q a r - affineRestore s b r) ∧
    innerWeightedNorm (-tau) (fun r => affineRestore q a r - affineRestore s b r) ≤
      innerDecayNorm tau (by linarith) * C + ‖a - b‖ * innerWeightedNorm (-tau) model := by
  have hqdiff := bounded_continuous_inWeightedL2_neg tau (by linarith) _ (hq.sub hs) C hC
  have h := innerWeighted_sub_const_mul_bound (-tau) (fun r => q r - s r) model
    hqdiff (affineModel_inWeightedL2_neg tau htau) (-(a - b))
  have heq : (fun r => affineRestore q a r - affineRestore s b r) =
      (fun r => (q r - s r) - (-(a - b)) * model r) := by
    funext r
    unfold affineRestore
    ring
  rw [heq]
  refine ⟨h.1, h.2.trans ?_⟩
  rw [norm_neg]
  exact _root_.add_le_add (innerWeightedNorm_le_of_bound tau (by linarith) _ (hq.sub hs) C hC) le_rfl
end HBL.Modulation.Monopole
