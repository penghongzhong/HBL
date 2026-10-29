import HBL.KummerBoundaryUnique.PerturbedUniqueness
import HBL.KummerBoundaryUnique.ResidualBound
import HBL.KummerCompactFamily.SmallBaseInverse
import HBL.KummerCompactFamily.PhysicalAnalytic
import HBL.KummerParameterInverse.ClassicalCertificate
import HBL.KummerParameterInverse.OperatorLipschitz
import HBL.KummerParameterInverse.SourceStability
import HBL.KummerParameterInverse.OperatorDerivative
import HBL.KummerParameterInverse.PhysicalParameterDerivatives
import HBL.KummerParameterInverse.CoefficientDifference
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem exists_actual_bounded_parameter_kummer_unique_family (z M : ℝ) (hz : 0 < z) (hM : 0 ≤ M) :
    ∃ eps d B : ℝ, 0 < eps ∧ 0 < d ∧ d < eps ∧ 0 < B ∧
      ∃ K : LocalKummerPair 0 0 z eps,
      ∃ S : (ℝ × ℝ) → (AnnulusSource z d →L[ℂ] AnnulusJet z d),
        0 < z - d ∧
        (∀ p : ℝ × ℝ, |p.1| + |p.2| ≤ M →
          IsKummerInverseAtCoefficient K d (frozenZeroCoeff p.1 p.2) (S p) ∧
          ‖S p‖ ≤ 2 * B ∧ ContDiffAt ℝ ω S p ∧
          HasDerivAt (fun m : ℝ => S (m,p.2)) (Complex.I • ((S p).comp (annulusValueOperator (S p)))) p.1 ∧
          HasDerivAt (fun t : ℝ => S (p.1,t)) (-((S p).comp (annulusValueOperator (S p)))) p.2 ∧
          (∀ F G : AnnulusSource z d, ‖S p F - S p G‖ ≤ (2 * B) * ‖F - G‖) ∧
          (∀ F U, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) F U ↔ U = S p F) ∧
          (∀ F G U, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) G U →
            ‖U - S p F‖ ≤ (2 * B) * ‖G-F‖)) ∧
        (∀ p q : ℝ × ℝ, |p.1| + |p.2| ≤ M → |q.1| + |q.2| ≤ M →
          ‖S p - S q‖ ≤ (4 * B ^ 2) * (|p.1 - q.1| + |p.2 - q.2|)) := by
  obtain ⟨eps,d,B,heps,hd,hde,hB,K,T,hpos,hT,hcert,hsmall⟩ := exists_small_baseKummer_inverse z M hz hM
  let S := fun p : ℝ × ℝ => annulusParameterInverse T (frozenZeroCoeff p.1 p.2 - frozenZeroCoeff 0 0)
  have hbound : ∀ p : ℝ × ℝ, |p.1| + |p.2| ≤ M →
      ‖frozenZeroCoeff p.1 p.2 - frozenZeroCoeff 0 0‖ * B ≤ (1 / 2 : ℝ) := by
    intro p hp
    have hnorm : ‖frozenZeroCoeff p.1 p.2 - frozenZeroCoeff 0 0‖ ≤ M := by
      calc
        _ ≤ |p.1| + |p.2| := by simpa only [sub_zero] using frozenZeroCoeff_difference_norm_le p.1 p.2 0 0
        _ ≤ M := hp
    have h := mul_le_mul_of_nonneg_right hnorm hB.le
    nlinarith
  refine ⟨eps,d,B,heps,hd,hde,hB,K,S,hpos,?_,?_⟩
  · intro p hp
    have hδ := hbound p hp
    have hs := (mul_le_mul_of_nonneg_left hT (norm_nonneg (frozenZeroCoeff p.1 p.2 - frozenZeroCoeff 0 0))).trans hδ
    have hc := annulusParameterInverse_classical K T hcert _ hs
    have he : frozenZeroCoeff 0 0 + (frozenZeroCoeff p.1 p.2 - frozenZeroCoeff 0 0) = frozenZeroCoeff p.1 p.2 := by ring
    rw [he] at hc
    have hu : ∀ F U, IsKummerBoundarySolution K d (frozenZeroCoeff p.1 p.2) F U ↔ U = S p F := by
      intro F U
      simpa only [he] using annulusParameterInverse_boundary_iff K hd hde T hcert _ hs F U
    have hnormS : ‖S p‖ ≤ 2 * B := annulusParameterInverse_norm_le T B hB.le hT _ hδ
    have hj := kummer_physical_parameter_derivatives (annulusParameterInverse T) _ p.1 p.2 0 0
      (annulusParameterInverse_hasDerivAt T _ hs)
    refine ⟨hc,hnormS,
      annulusPhysicalParameterInverse_contDiffAt T p hs,?_,hj.2,
      annulusParameterInverse_source_stability T B hB.le hT _ hδ, hu,
      kummer_boundary_residual_bound K _ (S p) (2*B) hnormS hu⟩
    have hm := hj.1
    rw [neg_smul_neg Complex.I ((S p).comp (annulusValueOperator (S p)))] at hm
    exact hm
  · intro p q hp hq
    have h := annulusParameterInverse_lipschitz T B hB.le hT _ _ (hbound p hp) (hbound q hq)
    have he : (frozenZeroCoeff p.1 p.2 - frozenZeroCoeff 0 0) - (frozenZeroCoeff q.1 q.2 - frozenZeroCoeff 0 0) =
        frozenZeroCoeff p.1 p.2 - frozenZeroCoeff q.1 q.2 := by ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (frozenZeroCoeff_difference_norm_le p.1 p.2 q.1 q.2) (by positivity))
end HBL.Profile.Kummer
