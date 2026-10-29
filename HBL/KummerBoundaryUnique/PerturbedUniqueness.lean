import HBL.KummerBoundaryUnique.BaseUniqueness
import HBL.KummerBoundaryUnique.CertificateSolution
import HBL.KummerBoundaryUnique.CoefficientShift
import HBL.KummerParameterInverse.ClassicalCertificate
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_boundary_iff {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (hd : 0 < d) (hde : d < eps)
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d)
    (hT : IsLocalKummerRightInverse K d T)
    (δ : ℂ) (hsmall : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ))
    (F : AnnulusSource z d) (U : AnnulusJet z d) :
    IsKummerBoundarySolution K d (frozenZeroCoeff mu theta + δ) F U ↔
      U = annulusParameterInverse T δ F := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  constructor
  · intro hU
    let G := F - δ • annulusValueProjection z d U
    have hshift : IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) G U :=
      kummer_boundary_solution_shift K _ δ F U hU
    have hbase := kummer_inverse_boundary_solution K hd (frozenZeroCoeff mu theta) T hT G
    have hu : U = T G := kummer_base_boundary_solution_unique K hd hde G U (T G) hshift hbase
    have hblock : annulusParameterBlock T δ G = F := by
      change G + δ • annulusValueProjection z d (T G) = F
      rw [← hu]
      exact sub_add_cancel F _
    have hinv := congrArg (fun A : AnnulusSource z d →L[ℂ] AnnulusSource z d => A G)
      (annulusParameterResolvent_identities T δ hsmall).2
    change annulusParameterResolvent T δ (annulusParameterBlock T δ G) = G at hinv
    rw [hblock] at hinv
    change U = T (annulusParameterResolvent T δ F)
    rw [hinv]
    exact hu
  · intro hU
    rw [hU]
    exact kummer_inverse_boundary_solution K hd _ _
      (annulusParameterInverse_classical K T hT δ hsmall) F
end HBL.Profile.Kummer
