import HBL.KummerParameterInverse.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

/-- A classical first-order jet on the closed annulus, with the fixed separated
endpoint conditions. Values outside the annulus are immaterial. -/
def IsKummerBoundarySolution {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps) (d : ℝ) (c : ℂ)
    (F : AnnulusSource z d) (U : AnnulusJet z d) : Prop :=
  ∃ u v : ℝ → ℂ,
    (∀ r : PhysicalAnnulus z d, U r = (u r, v r)) ∧
    (∀ (r : ℝ) (hr : r ∈ PhysicalAnnulus z d),
      HasDerivAt u (v r) r ∧
      HasDerivAt v (F ⟨r,hr⟩ - frozenFirstCoeff r * v r - c * u r) r) ∧
    (u (z + d) * K.dpsi d - v (z + d) * K.psi d = 0) ∧
    (K.phi (-d) * v (z - d) - K.dphi (-d) * u (z - d) = 0)
end HBL.Profile.Kummer
