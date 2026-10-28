import HBL.KummerLocalInverse.OperatorDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localKummerJetOperator_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d C : ℝ)
    (hd : 0 < d) (hde : d < eps) (hC : 0 ≤ C) (hK : LocalKummerBound K C) :
    ‖localKummerJetOperator K d C hd hde hC hK‖ ≤ 4 * d * C ^ 3 := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity) (localKummerJet_norm_le K d C hd hde hC hK)
end HBL.Profile.Kummer
