import HBL.KummerLocalInverse.SourceExtension
import HBL.KummerLocalInverse.PhysicalDerivatives
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

variable {mu theta z eps : ℝ}

/-- The value and actual radial derivative, as one continuous jet on the compact annulus. -/
def localKummerJet (K : LocalKummerPair mu theta z eps) (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : C(PhysicalAnnulus z d, ℂ)) : C(PhysicalAnnulus z d, ℂ × ℂ) where
  toFun r := (physicalLocalKummerValue K d (annulusSourceExtension z d hd.le F) r,
    physicalLocalKummerDeriv K d (annulusSourceExtension z d hd.le F) r)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro r
    have h := physicalLocalKummer_hasDerivAt K d hd hde _ (annulusSourceExtension_properties z d hd.le F).1 r.property
    exact (h.1.continuousAt.prodMk h.2.continuousAt).comp continuous_subtype_val.continuousAt
end HBL.Profile.Kummer
