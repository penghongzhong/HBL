import HBL.KummerParameterInverse.OperatorDifference
import HBL.KummerParameterInverse.OperatorBound
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_lipschitz {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (B : ℝ) (hB : 0 ≤ B)
    (hT : ‖T‖ ≤ B) (δ η : ℂ)
    (hδ : ‖δ‖ * B ≤ (1 / 2 : ℝ)) (hη : ‖η‖ * B ≤ (1 / 2 : ℝ)) :
    ‖annulusParameterInverse T δ - annulusParameterInverse T η‖ ≤ (4 * B ^ 2) * ‖δ - η‖ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  let : NormedAddCommGroup (AnnulusSource z d →L[ℂ] AnnulusJet z d) := inferInstance
  let : NormedSpace ℂ (AnnulusSource z d →L[ℂ] AnnulusJet z d) := inferInstance
  have hsδ := (mul_le_mul_of_nonneg_left hT (norm_nonneg δ)).trans hδ
  have hsη := (mul_le_mul_of_nonneg_left hT (norm_nonneg η)).trans hη
  rw [annulusParameterInverse_sub T δ η hsδ hsη, norm_smul]
  have hnδ := annulusParameterInverse_norm_le T B hB hT δ hδ
  have hnη := (annulusValueOperator_norm_le (annulusParameterInverse T η)).trans
    (annulusParameterInverse_norm_le T B hB hT η hη)
  calc
    _ ≤ ‖η - δ‖ * (‖annulusParameterInverse T δ‖ * ‖annulusValueOperator (annulusParameterInverse T η)‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖η - δ‖ * ((2 * B) * (2 * B)) := by gcongr
    _ = _ := by rw [norm_sub_rev η δ]; ring
end HBL.Profile.Kummer
