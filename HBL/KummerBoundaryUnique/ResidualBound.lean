import HBL.KummerBoundaryUnique.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

/-- A residual bound for any classical boundary jet, not only the constructed solution. -/
theorem kummer_boundary_residual_bound {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (c : ℂ)
    (S : AnnulusSource z d →L[ℂ] AnnulusJet z d) (C : ℝ) (hS : ‖S‖ ≤ C)
    (hunique : ∀ G U, IsKummerBoundarySolution K d c G U ↔ U = S G)
    (F G : AnnulusSource z d) (U : AnnulusJet z d)
    (hU : IsKummerBoundarySolution K d c G U) :
    ‖U - S F‖ ≤ C * ‖G-F‖ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  rw [(hunique G U).mp hU, ← map_sub]
  exact (S.le_opNorm (G-F)).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
end HBL.Profile.Kummer
