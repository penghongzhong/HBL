import HBL.KummerCompactFamily.RadiusChoice
import HBL.KummerLocalInverse.ActualPair
import HBL.KummerLocalInverse.OperatorCertificate
import HBL.KummerLocalInverse.OperatorBound
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem exists_small_baseKummer_inverse (z M : ℝ) (hz : 0 < z) (hM : 0 ≤ M) :
    ∃ eps d B : ℝ, 0 < eps ∧ 0 < d ∧ d < eps ∧ 0 < B ∧
      ∃ K : LocalKummerPair 0 0 z eps,
      ∃ T : C(PhysicalAnnulus z d, ℂ) →L[ℂ] C(PhysicalAnnulus z d, ℂ × ℂ),
        0 < z - d ∧ ‖T‖ ≤ B ∧ IsLocalKummerRightInverse K d T ∧ (M + 1) * B ≤ (1 / 4 : ℝ) := by
  obtain ⟨eps,C,heps,hC,K,hK⟩ := exists_actual_bounded_localKummerPair 0 0 z hz
  obtain ⟨d,B,hd,hde,hB,hBeq,hsmall⟩ := exists_common_kummer_radius eps C M heps hC hM
  let T := localKummerJetOperator K d C hd hde hC.le hK
  have hpos := K.radial_pos (-d) ⟨by linarith,by linarith⟩
  refine ⟨eps,d,B,heps,hd,hde,hB,K,T,by simpa only [sub_eq_add_neg] using hpos,?_,?_,hsmall⟩
  · rw [hBeq]
    exact localKummerJetOperator_norm_le K d C hd hde hC.le hK
  · exact localKummerJetOperator_rightInverse K d C hd hde hC.le hK
end HBL.Profile.Kummer
