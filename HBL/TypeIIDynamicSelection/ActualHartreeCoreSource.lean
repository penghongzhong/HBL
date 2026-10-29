import HBL.TypeIIDynamicSelection.ActualMovingRemoteFullSource
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# Quantitative SAME-EQUATION Hartree first-layer source bound

The left-hand side is the complete physical complex radial Hartree
renormalized residual of a real truncated monopole profile PLUS genuine
remote complex radiation with a MOVING support radius, minus the
stationary bubble residual. The bound is derived by combining the proven
physical effective-core Hartree estimate with the actual Riesz exterior
potential identity. It is NOT an abstract source/solver right-inverse
claim and uses no prescribed terminal modulation limit.

The remaining scalar |c-C_F| and source-mass input must be constructed
and estimated by the actual outer radiation/finite profile. Thus this
theorem does not close the full original manuscript layer 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation HBL.Modulation.AffineTail

/-- For the physical radial inverse-square Hartree nonlinearity, the
actual first-order core source has a fully explicit quadratic monopole
remainder and the true remote quartic-density scalar mass discrepancy.
All source, support, and differentiability assumptions are primitive.
The constant D is constructed by the proved actual core estimate. -/
theorem actual_physical_Hartree_first_layer_core_source_bound
    (c b omega R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r cs : ℝ}
    (hcs : HasDerivAt c cs s)
    (hc : |c s| ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hRc : ContinuousAt R s) (hR : 0 < R s)
    (hsep : 2 * r ≤ R s)
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
    ∃ D : ℝ, 0 < D ∧
      ‖complexRadialRenormalizedResidual
          (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
        complexRadialRenormalizedResidual
          (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r‖ ≤
        (monopoleStaticRadialBoundConstant * (c s) ^ 2 +
         monopoleRadialBoundConstant * |cs| +
         D * |b s * c s| +
         monopoleRadialBoundConstant * |omega s * c s|) +
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
  obtain ⟨D, hDpos, hD⟩ := monopoleComplexEffectiveIncrement_core_bound
  refine ⟨D, hDpos, ?_⟩
  have hcr : |c s| * r ≤ 1 := by
    calc
      |c s| * r ≤ |c s| * 1 :=
        mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)
      _ ≤ 1 := by simpa using hc
  have hcore : |c s| * r / 4 ≤ (1 / 2 : ℝ) := by linarith
  have heff := hD c cs s r (b s) (omega s) hcs hc hr hcore
  have hmis := actual_moving_remote_mass_mismatch_bound
    c b omega R Z hRc hR hr hsep hZ hVmeas hZmeas hF hVrow hc
  let E : ℂ := monopoleComplexEffectiveIncrement c (b s) (omega s) s r
  let P : ℂ :=
    complexRadialRenormalizedResidual
        (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
      complexRadialRenormalizedResidual
        (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r
  have htri : ‖P‖ ≤ ‖E‖ + ‖E - P‖ := by
    calc
      ‖P‖ = ‖E - (E - P)‖ := by congr 1; abel
      _ ≤ ‖E‖ + ‖E - P‖ := norm_sub_le _ _
  exact htri.trans (add_le_add heff hmis)

end HBL.TypeIIDynamicSelection
