import HBL.TypeIIDynamicSelection.PhysicalResidualMatch
import HBL.TypeIIDynamicSelection.ExteriorSpatialGain

/-!
# Physical source matching without ASSUMING exact mass cancellation

For the actual complex Hartree remote radiation, the discrepancy between
the effective monopole source and the FULL genuine PDE residual is bounded
by TWO explicitly displayed, different errors:

1. The physical scalar compatibility mismatch |c(s)-C_F(s)|, where C_F is
   the true nonlocal exterior mass of every quartic cross density.
2. The genuinely small geometric error O((r/R)^2) times exterior L1 mass.

This theorem does not postulate the desired c=C_F equality and does not
hide it in an arbitrary right-inverse package. The full nonlinear
three-region construction must solve the scalar compatibility equation
or prove that its mismatch has integrable temporal decay.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation HBL.Modulation.AffineTail

/-- The exact Hartree PDE residual differs from the effective inner source
by a physical exterior-mass mismatch and the (r/R)^2 error. No terminal
rate or numerical modulation limit is prescribed. -/
theorem actual_fullHartree_effective_mismatch_norm_le
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {R s r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hZ : ∀ t rho, rho ≤ R → Z t rho = 0)
    (hVmeas : Measurable (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s)))
    (hZmeas : Measurable (Z s))
    (hF : IntegrableOn (remoteComplexQuarticDifference
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s)) (Z s)) (Ioi R))
    (hVrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c s)) (c s) rho : ℂ)‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hc : |c s| ≤ 1) :
    ‖monopoleComplexEffectiveIncrement c (b s) (omega s) s r -
      (complexRadialRenormalizedResidual
        (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
       complexRadialRenormalizedResidual
         (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r)‖ ≤
    (|c s -
       radialHartreeExteriorCenter
         (remoteComplexQuarticDifference
           (monopolePerturbedRadialProfile
             (monopoleQuadraticRadius (c s)) (c s)) (Z s)) R| +
     (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / R ^ 2)) *
       ∫ rho in Ioi R,
         |remoteComplexQuarticDifference
           (monopolePerturbedRadialProfile
             (monopoleQuadraticRadius (c s)) (c s)) (Z s) rho|) *
     (1 + monopoleRadialBoundConstant) ^ 3 := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s)
  let F : ℝ → ℝ := remoteComplexQuarticDifference V (Z s)
  have heq := actual_full_radial_residual_remote_eq_exterior_increment
    c b omega Z hR hr hsep hZ hVmeas hZmeas hF hVrow
  rw [heq, monopoleEffective_minus_actualExterior_exact]
  have hFm : Measurable F :=
    remoteComplexQuarticDifference_measurable V (Z s) hVmeas hZmeas
  have hpot := actual_exteriorHartree_center_gap_L1_le
    F hFm hF hR hr hsep
  have htri := abs_add_le
    (c s - radialHartreeExteriorCenter F R)
    (radialHartreeExteriorCenter F R - radialHartreeExteriorPotential F R r)
  have hsum : (c s - radialHartreeExteriorCenter F R) +
      (radialHartreeExteriorCenter F R -
        radialHartreeExteriorPotential F R r) =
      c s - radialHartreeExteriorPotential F R r := by ring
  rw [hsum] at htri
  have hdiff : |c s - radialHartreeExteriorPotential F R r| ≤
      |c s - radialHartreeExteriorCenter F R| +
      (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / R ^ 2)) *
        ∫ rho in Ioi R, |F rho| := by
    exact htri.trans (add_le_add_left (by simpa only [abs_sub_comm] using hpot) _)
  have hv := monopolePerturbedRadialProfile_abs_le
    (R := monopoleQuadraticRadius (c s)) hr hc
  have hpow : |V r| ^ 3 ≤ (1 + monopoleRadialBoundConstant) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hv 3
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul hdiff hpow (by positivity)
    ((abs_nonneg _).trans hdiff)

end HBL.TypeIIDynamicSelection
