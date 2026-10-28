import HBL.KummerLocalInverse.JetDefinitions
import HBL.KummerLocalInverse.PhysicalLinearity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localKummerJet_add_smul
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ)
    (hd : 0 < d) (hde : d < eps) (F G : C(PhysicalAnnulus z d, ℂ)) (c : ℂ) :
    localKummerJet K d hd hde (F + c • G) = localKummerJet K d hd hde F + c • localKummerJet K d hd hde G := by
  have he : annulusSourceExtension z d hd.le (F + c • G) =
      (fun r => annulusSourceExtension z d hd.le F r + c * annulusSourceExtension z d hd.le G r) := rfl
  apply ContinuousMap.ext
  intro r
  have h := physicalLocalKummer_linear K d hd.le hde.le _ _
    (annulusSourceExtension_properties z d hd.le F).1 (annulusSourceExtension_properties z d hd.le G).1 c r.property
  change (physicalLocalKummerValue K d (annulusSourceExtension z d hd.le (F + c • G)) r,
    physicalLocalKummerDeriv K d (annulusSourceExtension z d hd.le (F + c • G)) r) = _
  rw [he]
  exact Prod.ext h.1 h.2
end HBL.Profile.Kummer
