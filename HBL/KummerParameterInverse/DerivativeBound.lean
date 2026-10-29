import HBL.KummerParameterInverse.OperatorDerivative
import HBL.KummerParameterInverse.OperatorBound
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_deriv_norm_le {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (B : ℝ) (hB : 0 ≤ B)
    (hT : ‖T‖ ≤ B) (δ : ℂ) (hδ : ‖δ‖ * B ≤ (1 / 2 : ℝ)) :
    ‖deriv (annulusParameterInverse T) δ‖ ≤ 4 * B ^ 2 := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  let : NormedAddCommGroup (AnnulusSource z d →L[ℂ] AnnulusJet z d) := inferInstance
  let : NormedSpace ℂ (AnnulusSource z d →L[ℂ] AnnulusJet z d) := inferInstance
  have hs := (mul_le_mul_of_nonneg_left hT (norm_nonneg δ)).trans hδ
  rw [(annulusParameterInverse_hasDerivAt T δ hs).deriv, norm_neg]
  have hn := annulusParameterInverse_norm_le T B hB hT δ hδ
  have hv := (annulusValueOperator_norm_le (annulusParameterInverse T δ)).trans hn
  calc
    _ ≤ ‖annulusParameterInverse T δ‖ * ‖annulusValueOperator (annulusParameterInverse T δ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (2 * B) * (2 * B) := mul_le_mul hn hv (norm_nonneg _) (by positivity)
    _ = _ := by ring
end HBL.Profile.Kummer
