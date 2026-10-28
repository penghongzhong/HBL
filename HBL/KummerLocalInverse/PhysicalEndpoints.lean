import HBL.KummerLocalInverse.PhysicalDefinitions
import HBL.KummerLocalInverse.EndpointNormalization
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem physicalLocalKummer_endpoint_normalization
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ) (F : ℝ → ℂ) :
    physicalLocalKummerValue K d F (z + d) * K.dpsi d - physicalLocalKummerDeriv K d F (z + d) * K.psi d = 0 ∧
    K.phi (-d) * physicalLocalKummerDeriv K d F (z - d) - K.dphi (-d) * physicalLocalKummerValue K d F (z - d) = 0 := by
  have h := (localAnnulus_endpoint_normalization K (-d) d (fun t => F (z + t))).2.2
  simpa only [physicalLocalKummerValue, physicalLocalKummerDeriv,
    add_sub_cancel_left, sub_sub_cancel_left] using h
end HBL.Profile.Kummer
