import HBL.KummerParameterInverse.ActualComplexFamily
import HBL.KummerParameterInverse.CoefficientDifference
import HBL.KummerParameterInverse.PhysicalParameterDerivatives
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem exists_actual_localKummer_uniform_physical_family (mu0 theta0 z : ℝ) (hz : 0 < z) :
    ∃ eps B ρ : ℝ, 0 < eps ∧ 0 < B ∧ 0 < ρ ∧
      ∃ K : LocalKummerPair mu0 theta0 z eps,
      ∃ T : ℝ → ℝ → (AnnulusSource z (eps / 2) →L[ℂ] AnnulusJet z (eps / 2)),
        0 < z - eps / 2 ∧
        (∀ mu theta : ℝ, |mu - mu0| + |theta - theta0| ≤ ρ →
          IsKummerInverseAtCoefficient K (eps / 2) (frozenZeroCoeff mu theta) (T mu theta) ∧
          ‖T mu theta‖ ≤ 2 * B ∧
          HasDerivAt (fun m : ℝ => T m theta)
            (Complex.I • ((T mu theta).comp (annulusValueOperator (T mu theta)))) mu ∧
          HasDerivAt (fun t : ℝ => T mu t)
            (-((T mu theta).comp (annulusValueOperator (T mu theta)))) theta ∧
          ∀ F G : AnnulusSource z (eps / 2), ‖T mu theta F - T mu theta G‖ ≤ (2 * B) * ‖F - G‖) ∧
        (∀ mu theta nu phi : ℝ,
          |mu - mu0| + |theta - theta0| ≤ ρ → |nu - mu0| + |phi - theta0| ≤ ρ →
          ‖T mu theta - T nu phi‖ ≤ (4 * B ^ 2) * (|mu - nu| + |theta - phi|)) := by
  obtain ⟨eps,B,ρ,heps,hB,hρ,K,S,hpos,hS,hLip⟩ :=
    exists_actual_localKummer_complex_parameter_family mu0 theta0 z hz
  let T := fun mu theta : ℝ => S (frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0)
  refine ⟨eps,B,ρ,heps,hB,hρ,K,T,hpos,?_,?_⟩
  · intro mu theta hnear
    have hδ := (frozenZeroCoeff_difference_norm_le mu theta mu0 theta0).trans hnear
    have hs := hS (frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0) hδ
    have hc : frozenZeroCoeff mu0 theta0 + (frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0) = frozenZeroCoeff mu theta := by ring
    rw [hc] at hs
    have hd := kummer_physical_parameter_derivatives S _ mu theta mu0 theta0 hs.2.2.1
    refine ⟨hs.1,hs.2.1,?_,hd.2,hs.2.2.2.2⟩
    have hm := hd.1
    rw [neg_smul_neg Complex.I ((S (frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0)).comp
      (annulusValueOperator (S (frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0))))] at hm
    exact hm
  · intro mu theta nu phi hnear hnear'
    have hδ := (frozenZeroCoeff_difference_norm_le mu theta mu0 theta0).trans hnear
    have hη := (frozenZeroCoeff_difference_norm_le nu phi mu0 theta0).trans hnear'
    have h := hLip _ _ hδ hη
    have he : (frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0) -
        (frozenZeroCoeff nu phi - frozenZeroCoeff mu0 theta0) = frozenZeroCoeff mu theta - frozenZeroCoeff nu phi := by ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (frozenZeroCoeff_difference_norm_le mu theta nu phi) (by positivity))
end HBL.Profile.Kummer
