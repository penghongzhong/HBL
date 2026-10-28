import HBL.KummerLocalInverse.OperatorBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localKummerJetOperator_difference_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d C : ℝ)
    (hd : 0 < d) (hde : d < eps) (hC : 0 ≤ C) (hK : LocalKummerBound K C)
    (F G : C(PhysicalAnnulus z d, ℂ)) :
    ‖localKummerJetOperator K d C hd hde hC hK F - localKummerJetOperator K d C hd hde hC hK G‖ ≤
      (4 * d * C ^ 3) * ‖F - G‖ := by
  rw [← map_sub]
  exact ((localKummerJetOperator K d C hd hde hC hK).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (localKummerJetOperator_norm_le K d C hd hde hC hK) (norm_nonneg _))
end HBL.Profile.Kummer
