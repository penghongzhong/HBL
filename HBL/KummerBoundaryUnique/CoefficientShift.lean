import HBL.KummerBoundaryUnique.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_boundary_solution_shift {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (c δ : ℂ)
    (F : AnnulusSource z d) (U : AnnulusJet z d)
    (hU : IsKummerBoundarySolution K d (c+δ) F U) :
    IsKummerBoundarySolution K d c (F - δ • annulusValueProjection z d U) U := by
  obtain ⟨u,v,hjet,hD,hp,hm⟩ := hU
  refine ⟨u,v,hjet,?_,hp,hm⟩
  intro r hr
  refine ⟨(hD r hr).1, ?_⟩
  convert (hD r hr).2 using 1
  change F ⟨r,hr⟩ - δ * (U ⟨r,hr⟩).1 - _ - _ = _
  rw [hjet]
  ring
end HBL.Profile.Kummer
