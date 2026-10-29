import HBL.KummerBoundaryUnique.BoundedUniqueFamily
import HBL.KummerCompactFamily.CompactParameterBound
import HBL.KummerCompactFamily.CompactJetBound
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem exists_actual_compact_parameter_kummer_unique_family (z : ℝ) (hz : 0 < z)
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) :
    ∃ eps d B : ℝ, 0 < eps ∧ 0 < d ∧ d < eps ∧ 0 < B ∧
      ∃ K : LocalKummerPair 0 0 z eps,
      ∃ S : (ℝ × ℝ) → (AnnulusSource z d →L[ℂ] AnnulusJet z d),
        0 < z - d ∧
        (∀ p ∈ A,
          IsKummerInverseAtCoefficient K d (frozenZeroCoeff p.1 p.2) (S p) ∧
          ‖S p‖ ≤ 2 * B ∧ ContDiffAt ℝ ω S p ∧
          HasDerivAt (fun m : ℝ => S (m,p.2)) (Complex.I • ((S p).comp (annulusValueOperator (S p)))) p.1 ∧
          HasDerivAt (fun t : ℝ => S (p.1,t)) (-((S p).comp (annulusValueOperator (S p)))) p.2 ∧
          (∀ F G : AnnulusSource z d, ‖S p F - S p G‖ ≤ (2 * B) * ‖F - G‖) ∧
          (∀ F U, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) F U ↔ U = S p F) ∧
          (∀ F G U, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) G U →
            ‖U - S p F‖ ≤ (2 * B) * ‖G-F‖)) ∧
        (∀ p ∈ A, ∀ q ∈ A, ‖S p - S q‖ ≤ (4 * B ^ 2) * (|p.1 - q.1| + |p.2 - q.2|)) ∧
        (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ A, ‖iteratedFDeriv ℝ n S p‖ ≤ C) := by
  obtain ⟨M,hM,hAM⟩ := compact_parameters_abs_bound A hA
  obtain ⟨eps,d,B,heps,hd,hde,hB,K,S,hpos,hS,hLip⟩ := exists_actual_bounded_parameter_kummer_unique_family z M hz hM
  refine ⟨eps,d,B,heps,hd,hde,hB,K,S,hpos,?_,?_,?_⟩
  · intro p hp
    exact hS p (hAM p hp)
  · intro p hp q hq
    exact hLip p q (hAM p hp) (hAM q hq)
  · exact compact_operator_parameter_jets_bounded A hA S (fun p hp => (hS p (hAM p hp)).2.2.1)
end HBL.Profile.Kummer
