import HBL.KummerParameterInverse.ResolventDifference
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_sub {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ η : ℂ)
    (hδ : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) (hη : ‖η‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    annulusParameterInverse T δ - annulusParameterInverse T η =
      (η - δ) • ((annulusParameterInverse T δ).comp
        ((annulusValueProjection z d).comp (annulusParameterInverse T η))) := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  rw [annulusParameterInverse, annulusParameterInverse, ← ContinuousLinearMap.comp_sub,
    annulusParameterResolvent_sub T δ η hδ hη, ContinuousLinearMap.comp_smul]
  rfl
end HBL.Profile.Kummer
