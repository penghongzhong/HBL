import HBL.KummerParameterInverse.ResolventDerivative
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_hasDerivAt {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ)
    (hδ : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    HasDerivAt (annulusParameterInverse T)
      (-((annulusParameterInverse T δ).comp (annulusValueOperator (annulusParameterInverse T δ)))) δ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have h := (hasDerivAt_const δ T).clm_comp (annulusParameterResolvent_hasDerivAt T δ hδ)
  unfold annulusParameterInverse
  simpa only [ContinuousLinearMap.zero_comp, zero_add, ContinuousLinearMap.comp_neg,
    annulusParameterInverse, annulusValueOperator, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc] using! h
end HBL.Profile.Kummer
