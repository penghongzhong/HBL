import HBL.KummerParameterInverse.BlockUnit
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterResolvent_identities {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ)
    (hsmall : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    annulusParameterBlock T δ * annulusParameterResolvent T δ = 1 ∧
    annulusParameterResolvent T δ * annulusParameterBlock T δ = 1 := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  exact ⟨Ring.mul_inverse_cancel _ (annulusParameterBlock_isUnit T δ hsmall),
    Ring.inverse_mul_cancel _ (annulusParameterBlock_isUnit T δ hsmall)⟩
end HBL.Profile.Kummer
