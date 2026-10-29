import HBL.KummerParameterInverse.ResolventIdentities
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_classical {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps)
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (hT : IsLocalKummerRightInverse K d T)
    (δ : ℂ) (hδ : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    IsKummerInverseAtCoefficient K d (frozenZeroCoeff mu theta + δ) (annulusParameterInverse T δ) := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  intro F
  let G := annulusParameterResolvent T δ F
  obtain ⟨u,v,w,hjet,hD,hplus,hminus⟩ := hT G
  refine ⟨u,v,w,hjet,?_,hplus,hminus⟩
  intro r hr
  have hsource := congrArg (fun A : AnnulusSource z d →L[ℂ] AnnulusSource z d => A F ⟨r,hr⟩)
    (annulusParameterResolvent_identities T δ hδ).1
  change G ⟨r,hr⟩ + δ * (T G ⟨r,hr⟩).1 = F ⟨r,hr⟩ at hsource
  rw [hjet] at hsource
  refine ⟨(hD r hr).1, (hD r hr).2.1, ?_⟩
  calc
    _ = (deriv (deriv u) r + frozenFirstCoeff r * deriv u r + frozenZeroCoeff mu theta * u r) + δ * u r := by ring
    _ = G ⟨r,hr⟩ + δ * u r := by rw [(hD r hr).2.2]
    _ = F ⟨r,hr⟩ := hsource
end HBL.Profile.Kummer
