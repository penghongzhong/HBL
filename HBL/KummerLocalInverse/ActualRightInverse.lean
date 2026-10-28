import HBL.KummerLocalInverse.ActualPair
import HBL.KummerLocalInverse.OperatorCertificate
import HBL.KummerLocalInverse.OperatorStability
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem exists_actual_localKummer_bounded_rightInverse (mu theta z : ℝ) (hz : 0 < z) :
    ∃ eps C : ℝ, 0 < eps ∧ 0 < C ∧
      ∃ K : LocalKummerPair mu theta z eps,
      ∃ T : C(PhysicalAnnulus z (eps / 2), ℂ) →L[ℂ] C(PhysicalAnnulus z (eps / 2), ℂ × ℂ),
        0 < z - eps / 2 ∧ ‖T‖ ≤ 2 * eps * C ^ 3 ∧ IsLocalKummerRightInverse K (eps / 2) T ∧
        ∀ F G : C(PhysicalAnnulus z (eps / 2), ℂ), ‖T F - T G‖ ≤ (2 * eps * C ^ 3) * ‖F - G‖ := by
  obtain ⟨eps, C, heps, hC, K, hK⟩ := exists_actual_bounded_localKummerPair mu theta z hz
  have hd : 0 < eps / 2 := half_pos heps
  have hde : eps / 2 < eps := by linarith
  let T := localKummerJetOperator K (eps / 2) C hd hde hC.le hK
  have hpos := K.radial_pos (-eps / 2) ⟨by linarith, by linarith⟩
  refine ⟨eps, C, heps, hC, K, T, by linarith, ?_, ?_, ?_⟩
  · have h := localKummerJetOperator_norm_le K (eps / 2) C hd hde hC.le hK
    calc
      ‖T‖ ≤ _ := h
      _ = _ := by ring
  · exact localKummerJetOperator_rightInverse K (eps / 2) C hd hde hC.le hK
  · intro F G
    have h := localKummerJetOperator_difference_le K (eps / 2) C hd hde hC.le hK F G
    calc
      _ ≤ _ := h
      _ = _ := by ring
end HBL.Profile.Kummer
