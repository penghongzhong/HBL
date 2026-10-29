import HBL.KummerBoundaryUnique.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_boundary_solution_sub {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (c : ℂ)
    (F G : AnnulusSource z d) (U V : AnnulusJet z d)
    (hU : IsKummerBoundarySolution K d c F U)
    (hV : IsKummerBoundarySolution K d c G V) :
    IsKummerBoundarySolution K d c (F-G) (U-V) := by
  obtain ⟨u,v,hjet,hD,hp,hm⟩ := hU
  obtain ⟨u',v',hjet',hD',hp',hm'⟩ := hV
  refine ⟨u-u',v-v',?_,?_,?_,?_⟩
  · intro r
    change U r - V r = _
    rw [hjet,hjet']
    rfl
  · intro r hr
    refine ⟨(hD r hr).1.sub (hD' r hr).1, ?_⟩
    convert (hD r hr).2.sub (hD' r hr).2 using 1
    change (F ⟨r,hr⟩ - G ⟨r,hr⟩) - _ - _ = _
    simp only [Pi.sub_apply]
    ring
  · simp only [Pi.sub_apply]
    linear_combination hp-hp'
  · simp only [Pi.sub_apply]
    linear_combination hm-hm'
end HBL.Profile.Kummer
