import HBL.KummerBoundaryUnique.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_inverse_boundary_solution {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (hd : 0 < d) (c : ℂ)
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d)
    (hT : IsKummerInverseAtCoefficient K d c T) (F : AnnulusSource z d) :
    IsKummerBoundarySolution K d c F (T F) := by
  obtain ⟨u,v,w,hjet,hD,hplus,hminus⟩ := hT F
  have heq : ∀ r ∈ PhysicalAnnulus z d, deriv u r = v r := fun r hr => (hD r hr).1.deriv
  have hp : z + d ∈ PhysicalAnnulus z d := by constructor <;> linarith
  have hm : z - d ∈ PhysicalAnnulus z d := by constructor <;> linarith
  refine ⟨u,deriv u,?_,?_,?_,?_⟩
  · intro r
    rw [hjet, heq r r.property]
  · intro r hr
    refine ⟨(heq r hr).symm ▸ (hD r hr).1, ?_⟩
    convert (hD r hr).2.1 using 1
    have hw := (hD r hr).2.1.deriv
    have hode := (hD r hr).2.2
    rw [hw] at hode
    linear_combination -hode
  · simpa only [heq _ hp] using hplus
  · simpa only [heq _ hm] using hminus
end HBL.Profile.Kummer
