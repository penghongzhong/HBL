import HBL.TypeIIDynamicSelection.PhysicalSourceMismatch
import HBL.TypeIIDynamicSelection.ActualMovingRemoteResidual
import Mathlib.Tactic

/-!
# SAME physical Hartree residual with a moving exterior radiation region

An exterior complex radiation field with moving support does not alter
the renormalized local derivatives in the bubble core. Its full nonlinear
effect is the true radial inverse-square Hartree potential, including all
cross quartic density terms. The exact mismatch with the effective slow
monopole cubic is the actual exterior mass mismatch plus the O(r²/R²)
geometric error, with no imposed equality c = exterior mass.

This is a source-matching theorem, not existence of a PDE blowup orbit.
-/

noncomputable section
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation HBL.Modulation.AffineTail

/-- The TRUE full renormalized radial Hartree residual, with moving
remote radiation and all nonlocal quartic cross terms, has exactly the
exterior Riesz source on the core. No fixed-in-time cutoff is needed. -/
theorem actual_moving_remote_full_Hartree_source_exact
    (c b omega R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r : ℝ}
    (hRc : ContinuousAt R s) (hR : 0 < R s)
    (hr : 0 < r) (hsep : 2 * r ≤ R s)
    (hZ : ∀ t rho, rho ≤ R t → Z t rho = 0)
    (hVmeas : Measurable (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s)))
    (hZmeas : Measurable (Z s))
    (hF : IntegrableOn (remoteComplexQuarticDifference
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s)) (Z s)) (Ioi (R s)))
    (hVrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c s)) (c s) rho : ℂ)‖ ^ 4)
      (Ioi (0 : ℝ))) :
    complexRadialRenormalizedResidual
      (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
      complexRadialRenormalizedResidual
        (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r =
      monopoleExteriorHartreeIncrement
        (remoteComplexQuarticDifference
          (monopolePerturbedRadialProfile
            (monopoleQuadraticRadius (c s)) (c s)) (Z s))
        (R s) c b omega s r := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s)
  let F : ℝ → ℝ := remoteComplexQuarticDifference V (Z s)
  have hrR : r < R s := by linarith
  have hres := actual_full_radial_residual_moving_remote_eq_nonlin
    (s := s) c b omega R Z hRc hrR hZ
  have hn := actual_complexHartree_remote_quartic_source_exact
    V (Z s) hR hr hsep (hZ s) hVmeas hZmeas hF hVrow
  have hnonlin :
    complexRadialHartreeNonlinearity (monopoleWithRemoteRadiation c Z s) r -
      complexRadialHartreeNonlinearity (monopoleInnerComplexProfile c s) r =
      (radialHartreeExteriorPotential F (R s) r : ℂ) *
        (monopoleInnerComplexProfile c s r) ^ 3 := hn
  have hdelta :
    complexRadialRenormalizedResidual
        (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
      complexRadialRenormalizedResidual
        (monopoleInnerComplexProfile c) (b s) (omega s) s r =
      (radialHartreeExteriorPotential F (R s) r : ℂ) *
        (monopoleInnerComplexProfile c s r) ^ 3 :=
    hres.trans hnonlin
  calc
    complexRadialRenormalizedResidual
        (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
      complexRadialRenormalizedResidual
        (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r =
      (complexRadialRenormalizedResidual
        (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
       complexRadialRenormalizedResidual
         (monopoleInnerComplexProfile c) (b s) (omega s) s r) +
      (complexRadialRenormalizedResidual
        (monopoleInnerComplexProfile c) (b s) (omega s) s r -
       complexRadialRenormalizedResidual
         (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r) := by ring
    _ = monopoleExteriorHartreeIncrement F (R s) c b omega s r := by
      rw [hdelta]
      unfold monopoleExteriorHartreeIncrement monopoleInnerComplexProfile
      ring

/-- The physical moving-cutoff nonlinear source differs from the
effective monopole source only by the ACTUAL scalar mass mismatch and
the derived quadratic geometric source bound. No mass cancellation
is assumed to have been solved by the PDE construction. -/
theorem actual_moving_remote_mass_mismatch_bound
    (c b omega R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r : ℝ}
    (hRc : ContinuousAt R s) (hR : 0 < R s)
    (hr : 0 < r) (hsep : 2 * r ≤ R s)
    (hZ : ∀ t rho, rho ≤ R t → Z t rho = 0)
    (hVmeas : Measurable (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s)))
    (hZmeas : Measurable (Z s))
    (hF : IntegrableOn (remoteComplexQuarticDifference
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s)) (Z s)) (Ioi (R s)))
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
             (monopoleQuadraticRadius (c s)) (c s)) (Z s)) (R s)| +
     (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (R s) ^ 2)) *
       ∫ rho in Ioi (R s),
         |remoteComplexQuarticDifference
           (monopolePerturbedRadialProfile
             (monopoleQuadraticRadius (c s)) (c s)) (Z s) rho|) *
     (1 + monopoleRadialBoundConstant) ^ 3 := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s)
  let F : ℝ → ℝ := remoteComplexQuarticDifference V (Z s)
  have heq := actual_moving_remote_full_Hartree_source_exact
    c b omega R Z hRc hR hr hsep hZ hVmeas hZmeas hF hVrow
  rw [heq, monopoleEffective_minus_actualExterior_exact]
  have hFm : Measurable F :=
    remoteComplexQuarticDifference_measurable V (Z s) hVmeas hZmeas
  have hpot := actual_exteriorHartree_center_gap_L1_le
    F hFm hF hR hr hsep
  have htri := abs_add_le
    (c s - radialHartreeExteriorCenter F (R s))
    (radialHartreeExteriorCenter F (R s) -
      radialHartreeExteriorPotential F (R s) r)
  have hsum : (c s - radialHartreeExteriorCenter F (R s)) +
      (radialHartreeExteriorCenter F (R s) -
        radialHartreeExteriorPotential F (R s) r) =
      c s - radialHartreeExteriorPotential F (R s) r := by ring
  rw [hsum] at htri
  have hdiff : |c s - radialHartreeExteriorPotential F (R s) r| ≤
      |c s - radialHartreeExteriorCenter F (R s)| +
      (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (R s) ^ 2)) *
        ∫ rho in Ioi (R s), |F rho| := by
    exact htri.trans (add_le_add_right
      (by simpa only [abs_sub_comm] using hpot) _)
  have hv := monopolePerturbedRadialProfile_abs_le
    (R := monopoleQuadraticRadius (c s)) hr hc
  have hpow : |V r| ^ 3 ≤ (1 + monopoleRadialBoundConstant) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hv 3
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul hdiff hpow (by positivity)
    ((abs_nonneg _).trans hdiff)

end HBL.TypeIIDynamicSelection
