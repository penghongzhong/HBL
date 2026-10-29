import HBL.KummerPrescribedAnnulus.CompactPair
import HBL.KummerLocalInverse.OperatorCertificate
import HBL.KummerLocalInverse.OperatorStability
import HBL.KummerBoundaryUnique.BaseUniqueness
import HBL.KummerBoundaryUnique.CertificateSolution

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HBL.Profile.Kummer

/-- Uniform actual inversion and residual control on an input annulus for all
parameters in an input compact set, with center-normalized endpoint conditions. -/
theorem exists_compact_prescribed_kummer_inverse
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) (z d : ℝ) (hd : 0 < d) (hz : d < z) :
    ∃ eps C B : ℝ, d < eps ∧ eps < z ∧ 0 < C ∧ 0 < B ∧
      ∀ p ∈ A, ∃ K : LocalKummerPair p.1 p.2 z eps,
      ∃ T : AnnulusSource z d →L[ℂ] AnnulusJet z d,
        ‖T‖ ≤ B ∧ IsLocalKummerRightInverse K d T ∧
        (∀ F, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) F (T F)) ∧
        (∀ F U, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) F U → U = T F) ∧
        (∀ F G, ‖T F - T G‖ ≤ B * ‖F - G‖) ∧
        (∀ F H U, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) H U →
          ‖U - T F‖ ≤ B * ‖H - F‖) ∧ LocalKummerBound K C := by
  let eps := (z + d) / 2
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hde : d < eps := by dsimp [eps]; linarith
  have hez : eps < z := by dsimp [eps]; linarith
  obtain ⟨C, hC, hpairs⟩ := exists_compact_prescribed_kummer_pair A hA z eps heps hez
  refine ⟨eps, C, 4 * d * C ^ 3, hde, hez, hC, by positivity, ?_⟩
  intro p hp
  obtain ⟨K, hK⟩ := hpairs p hp
  let T := localKummerJetOperator K d C hd hde hC.le hK
  have hT : IsLocalKummerRightInverse K d T :=
    localKummerJetOperator_rightInverse K d C hd hde hC.le hK
  have hsol (F : AnnulusSource z d) :
      IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) F (T F) :=
    kummer_inverse_boundary_solution K hd (frozenZeroCoeff p.1 p.2) T hT F
  have huniq (F : AnnulusSource z d) (U : AnnulusJet z d)
      (hU : IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) F U) : U = T F :=
    kummer_base_boundary_solution_unique K hd hde F U (T F) hU (hsol F)
  have hstable (F G : AnnulusSource z d) :
      ‖T F - T G‖ ≤ (4 * d * C ^ 3) * ‖F - G‖ :=
    localKummerJetOperator_difference_le K d C hd hde hC.le hK F G
  refine ⟨K, T, localKummerJetOperator_norm_le K d C hd hde hC.le hK,
    hT, hsol, huniq, hstable, ?_, hK⟩
  intro F H U hU
  rw [huniq H U hU]
  exact hstable H F
end HBL.Profile.Kummer
