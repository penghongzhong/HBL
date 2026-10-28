import HBL.KummerLocalInverse.JetDefinitions
import HBL.KummerLocalInverse.PhysicalBounds
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localKummerJet_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d C : ℝ)
    (hd : 0 < d) (hde : d < eps) (hC : 0 ≤ C) (hK : LocalKummerBound K C)
    (F : C(PhysicalAnnulus z d, ℂ)) : ‖localKummerJet K d hd hde F‖ ≤ (4 * d * C ^ 3) * ‖F‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro r
  have h := physicalLocalKummer_norm_le K d C ‖F‖ hde.le hC (norm_nonneg _) hK _
    (fun s _ => (annulusSourceExtension_properties z d hd.le F).2.1 s) r.property
  change ‖(physicalLocalKummerValue K d (annulusSourceExtension z d hd.le F) r,
    physicalLocalKummerDeriv K d (annulusSourceExtension z d hd.le F) r)‖ ≤ _
  rw [Prod.norm_def]
  exact max_le ((le_add_of_nonneg_right (norm_nonneg _)).trans h)
    ((le_add_of_nonneg_left (norm_nonneg _)).trans h)
end HBL.Profile.Kummer
