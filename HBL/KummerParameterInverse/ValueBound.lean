import HBL.KummerParameterInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusValueOperator_norm_le {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) : ‖annulusValueOperator T‖ ≤ ‖T‖ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hP : ‖annulusValueProjection z d‖ ≤ 1 := by
    apply LinearMap.mkContinuous_norm_le _ (by norm_num)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg T))
end HBL.Profile.Kummer
