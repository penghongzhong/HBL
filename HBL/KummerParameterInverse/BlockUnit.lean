import HBL.KummerParameterInverse.ValueBound
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterBlock_isUnit {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ)
    (hsmall : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) : IsUnit (annulusParameterBlock T δ) := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have h : ‖-(δ • annulusValueOperator T)‖ < 1 := by
    rw [norm_neg, norm_smul]
    have hb := mul_le_mul_of_nonneg_left (annulusValueOperator_norm_le T) (norm_nonneg δ)
    linarith
  simpa only [sub_neg_eq_add, annulusParameterBlock] using IsUnit.one_sub_of_norm_lt_one (R := AnnulusSource z d →L[ℂ] AnnulusSource z d) h
end HBL.Profile.Kummer
