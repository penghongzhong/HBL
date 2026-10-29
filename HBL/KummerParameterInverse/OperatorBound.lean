import HBL.KummerParameterInverse.ResolventBound
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_norm_le {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (B : ℝ) (hB : 0 ≤ B)
    (hT : ‖T‖ ≤ B) (δ : ℂ) (hsmall : ‖δ‖ * B ≤ (1 / 2 : ℝ)) :
    ‖annulusParameterInverse T δ‖ ≤ 2 * B := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hs : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_left hT (norm_nonneg δ)).trans hsmall
  calc
    ‖annulusParameterInverse T δ‖ ≤ ‖T‖ * ‖annulusParameterResolvent T δ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * 2 := mul_le_mul hT (annulusParameterResolvent_norm_le T δ hs) (norm_nonneg _) hB
    _ = _ := by ring
end HBL.Profile.Kummer
