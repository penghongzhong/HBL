import HBL.KummerSourceTangents.ProjectionBound
import HBL.KummerBoundaryUnique.ResidualBound
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_source_tangent_residual_bound {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (c : ℂ)
    (S : AnnulusSource z d →L[ℂ] AnnulusJet z d) (C : ℝ) (hC : 0 ≤ C) (hn : ‖S‖ ≤ C)
    (hu : ∀ H W, IsKummerBoundarySolution K d c H W ↔ W = S H)
    (q : ℂ) (F G H J : AnnulusSource z d) (U V : AnnulusJet z d)
    (hU : IsKummerBoundarySolution K d c H U)
    (hV : IsKummerBoundarySolution K d c J V) :
    ‖V - annulusSourceTangent S q F G‖ ≤
      C * ‖J - G - q • annulusValueProjection z d U‖ + ‖q‖ * C^2 * ‖H-F‖ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hbase := kummer_boundary_residual_bound K c S C hn hu F H U hU
  have htan := kummer_boundary_residual_bound K c S C hn hu
    (G + q • annulusValueProjection z d (S F)) J V hV
  have he : J - (G + q • annulusValueProjection z d (S F)) =
      (J-G-q • annulusValueProjection z d U) + q • annulusValueProjection z d (U-S F) := by
    rw [map_sub, smul_sub]
    abel
  have hproj := (annulusValueProjection_apply_norm_le (U-S F)).trans hbase
  calc
    _ ≤ C * ‖J - (G + q • annulusValueProjection z d (S F))‖ := htan
    _ = C * ‖(J-G-q • annulusValueProjection z d U) + q • annulusValueProjection z d (U-S F)‖ := by rw [he]
    _ ≤ C * (‖J-G-q • annulusValueProjection z d U‖ + ‖q • annulusValueProjection z d (U-S F)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hC
    _ = C * (‖J-G-q • annulusValueProjection z d U‖ + ‖q‖ * ‖annulusValueProjection z d (U-S F)‖) := by rw [norm_smul]
    _ ≤ C * (‖J-G-q • annulusValueProjection z d U‖ + ‖q‖ * (C * ‖H-F‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hproj (norm_nonneg q))) hC
    _ = _ := by ring
end HBL.Profile.Kummer
