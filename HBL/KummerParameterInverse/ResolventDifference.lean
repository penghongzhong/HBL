import HBL.KummerParameterInverse.ResolventIdentities
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterResolvent_sub {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ η : ℂ)
    (hδ : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) (hη : ‖η‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    annulusParameterResolvent T δ - annulusParameterResolvent T η =
      (η - δ) • (annulusParameterResolvent T δ * annulusValueOperator T * annulusParameterResolvent T η) := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hu : IsUnit (annulusParameterBlock T δ) ↔ IsUnit (annulusParameterBlock T η) :=
    ⟨fun _ => annulusParameterBlock_isUnit T η hη, fun _ => annulusParameterBlock_isUnit T δ hδ⟩
  have hb : annulusParameterBlock T η - annulusParameterBlock T δ =
      (η - δ) • annulusValueOperator T := by
    unfold annulusParameterBlock
    rw [sub_smul η δ (annulusValueOperator T)]
    abel
  simpa only [annulusParameterResolvent, hb, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp] using Ring.inverse_sub_inverse hu
end HBL.Profile.Kummer
