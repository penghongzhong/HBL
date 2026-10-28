import HBL.KummerLocalInverse.SourceExtensionDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem annulusSourceExtension_properties (z d : ℝ) (hd : 0 ≤ d) (F : C(PhysicalAnnulus z d, ℂ)) :
    Continuous (annulusSourceExtension z d hd F) ∧
    (∀ r : ℝ, ‖annulusSourceExtension z d hd F r‖ ≤ ‖F‖) ∧
    (∀ (r : ℝ) (hr : r ∈ PhysicalAnnulus z d), annulusSourceExtension z d hd F r = F ⟨r, hr⟩) := by
  refine ⟨F.continuous.comp continuous_projIcc, fun r => F.norm_coe_le_norm _, ?_⟩
  intro r hr
  unfold annulusSourceExtension
  rw [projIcc_of_mem _ hr]
end HBL.Profile.Kummer
