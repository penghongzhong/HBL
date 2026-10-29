import HBL.KummerSourceTangents.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusValueProjection_apply_norm_le {z d : ℝ} (U : AnnulusJet z d) :
    ‖annulusValueProjection z d U‖ ≤ ‖U‖ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hP : ‖annulusValueProjection z d‖ ≤ 1 := by
    apply LinearMap.mkContinuous_norm_le _ (by norm_num)
  exact ((annulusValueProjection z d).le_opNorm U).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (norm_nonneg U))
end HBL.Profile.Kummer
