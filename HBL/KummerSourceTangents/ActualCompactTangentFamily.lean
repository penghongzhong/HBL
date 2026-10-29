import HBL.KummerBoundaryUnique.ActualCompactUniqueFamily
import HBL.KummerSourceTangents.CurveCertificate
import HBL.KummerSourceTangents.CoupledResidual
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem exists_actual_compact_kummer_source_tangent_family (z : ℝ) (hz : 0 < z)
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
            ‖U - S p F‖ ≤ (2 * B) * ‖G-F‖) ∧
          (∀ (F : (ℝ × ℝ) → AnnulusSource z d) (Fm Ft : AnnulusSource z d),
            HasDerivAt (fun m => F (m,p.2)) Fm p.1 →
            HasDerivAt (fun t => F (p.1,t)) Ft p.2 →
            KummerSourceTangentAt K (frozenZeroCoeff p.1 p.2) (2*B)
              (fun m => S (m,p.2)) (fun m => F (m,p.2)) p.1 Complex.I Fm ∧
            KummerSourceTangentAt K (frozenZeroCoeff p.1 p.2) (2*B)
              (fun t => S (p.1,t)) (fun t => F (p.1,t)) p.2 (-1) Ft) ∧
          (∀ (q : ℂ) (F G H J : AnnulusSource z d) (U V : AnnulusJet z d),
            IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) H U →
            IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) J V →
            ‖V - annulusSourceTangent (S p) q F G‖ ≤
              (2*B) * ‖J-G-q • annulusValueProjection z d U‖ + ‖q‖ * (2*B)^2 * ‖H-F‖)) ∧
        (∀ p ∈ A, ∀ q ∈ A, ‖S p - S q‖ ≤ (4 * B ^ 2) * (|p.1 - q.1| + |p.2 - q.2|)) ∧
        (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ A, ‖iteratedFDeriv ℝ n S p‖ ≤ C) := by
  obtain ⟨eps,d,B,heps,hd,hde,hB,K,S,hpos,hS,hLip,hjets⟩ :=
    exists_actual_compact_parameter_kummer_unique_family z hz A hA
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  refine ⟨eps,d,B,heps,hd,hde,hB,K,S,hpos,?_,hLip,hjets⟩
  intro p hp
  obtain ⟨hc,hn,hr,hm,ht,hs,hu,he⟩ := hS p hp
  refine ⟨hc,hn,hr,hm,ht,hs,hu,he,?_,?_⟩
  · intro F Fm Ft hFm hFt
    constructor
    · exact kummer_source_tangent_certificate K _ (2*B) (by positivity)
        (fun m => S (m,p.2)) (fun m => F (m,p.2)) p.1 Complex.I Fm hm hFm hc hn hu
    · apply kummer_source_tangent_certificate K _ (2*B) (by positivity)
        (fun t => S (p.1,t)) (fun t => F (p.1,t)) p.2 (-1) Ft _ hFt hc hn hu
      change HasDerivAt (fun t : ℝ => S (p.1,t))
        ((-1 : ℂ) • ((S p).comp (annulusValueOperator (S p)))) p.2
      rw [neg_one_smul ℂ ((S p).comp (annulusValueOperator (S p)))]
      exact ht
  · exact kummer_source_tangent_residual_bound K _ (S p) (2*B) (by positivity) hn hu
end HBL.Profile.Kummer
