import HBL.KummerParameterInverse.ResolventIdentities
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterResolvent_norm_le {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ)
    (hsmall : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) : ‖annulusParameterResolvent T δ‖ ≤ 2 := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro F
  let G := annulusParameterResolvent T δ F
  have h := congrArg (fun A : AnnulusSource z d →L[ℂ] AnnulusSource z d => A F)
    (annulusParameterResolvent_identities T δ hsmall).1
  change G + δ • annulusValueOperator T G = F at h
  have he : G = F - δ • annulusValueOperator T G := eq_sub_of_add_eq h
  have hVG : ‖annulusValueOperator T G‖ ≤ ‖T‖ * ‖G‖ :=
    (annulusValueOperator T).le_opNorm G |>.trans
      (mul_le_mul_of_nonneg_right (annulusValueOperator_norm_le T) (norm_nonneg G))
  have hn : ‖G‖ ≤ ‖F‖ + ‖δ‖ * (‖T‖ * ‖G‖) := by
    calc
      ‖G‖ = ‖F - δ • annulusValueOperator T G‖ := congrArg norm he
      _ ≤ ‖F‖ + ‖δ • annulusValueOperator T G‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_smul]; gcongr
  have hq := mul_le_mul_of_nonneg_right hsmall (norm_nonneg G)
  change ‖G‖ ≤ 2 * ‖F‖
  nlinarith
end HBL.Profile.Kummer
