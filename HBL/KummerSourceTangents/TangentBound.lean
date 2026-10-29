import HBL.KummerSourceTangents.ProjectionBound
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusSourceTangent_norm_le {z d : ℝ}
    (S : AnnulusSource z d →L[ℂ] AnnulusJet z d) (C : ℝ) (hC : 0 ≤ C)
    (hS : ‖S‖ ≤ C) (q : ℂ) (F G : AnnulusSource z d) :
    ‖annulusSourceTangent S q F G‖ ≤ C * ‖G‖ + ‖q‖ * C^2 * ‖F‖ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hSF : ‖S F‖ ≤ C * ‖F‖ := (S.le_opNorm F).trans
    (mul_le_mul_of_nonneg_right hS (norm_nonneg F))
  have hP := (annulusValueProjection_apply_norm_le (S F)).trans hSF
  calc
    _ ≤ C * ‖G + q • annulusValueProjection z d (S F)‖ :=
      (S.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
    _ ≤ C * (‖G‖ + ‖q • annulusValueProjection z d (S F)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hC
    _ = C * (‖G‖ + ‖q‖ * ‖annulusValueProjection z d (S F)‖) := by rw [norm_smul]
    _ ≤ C * (‖G‖ + ‖q‖ * (C * ‖F‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hP (norm_nonneg q))) hC
    _ = _ := by ring
end HBL.Profile.Kummer
