import HBL.KummerLocalInverse.OperatorDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

/-- Classical right inverse with two independent endpoint coefficient normalizations. -/
def IsLocalKummerRightInverse {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ)
    (T : C(PhysicalAnnulus z d, ℂ) →L[ℂ] C(PhysicalAnnulus z d, ℂ × ℂ)) : Prop :=
  ∀ F : C(PhysicalAnnulus z d, ℂ), ∃ u v w : ℝ → ℂ,
    (∀ r : PhysicalAnnulus z d, T F r = (u r, v r)) ∧
    (∀ (r : ℝ) (hr : r ∈ PhysicalAnnulus z d),
      HasDerivAt u (v r) r ∧ HasDerivAt (deriv u) (w r) r ∧
      deriv (deriv u) r + frozenFirstCoeff r * deriv u r + frozenZeroCoeff mu theta * u r = F ⟨r, hr⟩) ∧
    (u (z + d) * K.dpsi d - v (z + d) * K.psi d = 0) ∧
    (K.phi (-d) * v (z - d) - K.dphi (-d) * u (z - d) = 0)
end HBL.Profile.Kummer
