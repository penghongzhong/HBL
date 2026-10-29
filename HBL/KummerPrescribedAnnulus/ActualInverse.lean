import HBL.KummerPrescribedAnnulus.ActualPair
import HBL.KummerLocalInverse.OperatorCertificate
import HBL.KummerLocalInverse.OperatorStability
import HBL.KummerBoundaryUnique.BaseUniqueness
import HBL.KummerBoundaryUnique.CertificateSolution

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HBL.Profile.Kummer

/-- Actual normalized inverse on a prescribed positive annulus, with classical
endpoint derivatives, boundary uniqueness, stability and an equation-residual
error estimate. Neither a fundamental pair nor an inverse is an input. -/
theorem exists_actual_kummer_prescribed_annulus_inverse
    (mu theta z d : ℝ) (hd : 0 < d) (hz : d < z) :
    ∃ eps C : ℝ, d < eps ∧ eps < z ∧ 0 < C ∧
      ∃ K : LocalKummerPair mu theta z eps,
      ∃ T : AnnulusSource z d →L[ℂ] AnnulusJet z d,
        ‖T‖ ≤ 4 * d * C ^ 3 ∧ IsLocalKummerRightInverse K d T ∧
        (∀ F, IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) F (T F)) ∧
        (∀ F U, IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) F U → U = T F) ∧
        (∀ F G, ‖T F - T G‖ ≤ (4 * d * C ^ 3) * ‖F - G‖) ∧
        (∀ F H U, IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) H U →
          ‖U - T F‖ ≤ (4 * d * C ^ 3) * ‖H - F‖) := by
  let eps := (z + d) / 2
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hde : d < eps := by dsimp [eps]; linarith
  have hez : eps < z := by dsimp [eps]; linarith
  obtain ⟨C, hC, K, hK⟩ := exists_prescribed_bounded_kummer_pair mu theta z eps heps hez
  let T := localKummerJetOperator K d C hd hde hC.le hK
  have hT : IsLocalKummerRightInverse K d T :=
    localKummerJetOperator_rightInverse K d C hd hde hC.le hK
  have hsol (F : AnnulusSource z d) :
      IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) F (T F) :=
    kummer_inverse_boundary_solution K hd (frozenZeroCoeff mu theta) T hT F
  have huniq (F : AnnulusSource z d) (U : AnnulusJet z d)
      (hU : IsKummerBoundarySolution K d (frozenZeroCoeff mu theta) F U) : U = T F :=
    kummer_base_boundary_solution_unique K hd hde F U (T F) hU (hsol F)
  have hstable (F G : AnnulusSource z d) :
      ‖T F - T G‖ ≤ (4 * d * C ^ 3) * ‖F - G‖ :=
    localKummerJetOperator_difference_le K d C hd hde hC.le hK F G
  refine ⟨eps, C, hde, hez, hC, K, T,
    localKummerJetOperator_norm_le K d C hd hde hC.le hK, hT, hsol, huniq, hstable, ?_⟩
  intro F H U hU
  rw [huniq H U hU]
  exact hstable H F
end HBL.Profile.Kummer
