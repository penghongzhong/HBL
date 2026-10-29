import HBL.KummerParameterInverse.OperatorBound
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_source_stability {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (B : ℝ) (hB : 0 ≤ B)
    (hT : ‖T‖ ≤ B) (δ : ℂ) (hδ : ‖δ‖ * B ≤ (1 / 2 : ℝ))
    (F G : AnnulusSource z d) :
    ‖annulusParameterInverse T δ F - annulusParameterInverse T δ G‖ ≤ (2 * B) * ‖F - G‖ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  rw [← map_sub]
  exact ((annulusParameterInverse T δ).le_opNorm (F - G)).trans
    (mul_le_mul_of_nonneg_right (annulusParameterInverse_norm_le T B hB hT δ hδ) (norm_nonneg _))
end HBL.Profile.Kummer
