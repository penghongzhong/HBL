import HBL.TypeIIDynamicSelection.ActualKummerRepairFullDensityFeedback
import HBL.TypeIIDynamicSelection.ActualKummerRepairBackgroundEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import Mathlib.Tactic

/-!
# Complete Kummer-repair Hartree density feedback on the true background

This specializes the generic full quartic density-difference estimate to the
same physical background used in the HBL construction:
  U = V_c + Z_ell,
where V_c is the actual moment-locked moving Hartree monopole and Z_ell is
the critically rescaled genuine radiation.

The shell amplitude is not assumed: it is produced by the strict global
monopole decay and Strauss radiation estimate.  The theorem retains both:
* the full exterior center, with its physical shell-length cost aR;
* the non-center core error, with the geometric inverse-radius gain 1/(aR).

No upper bound on a, no remote center cancellation and no final Type-II rate
is inserted.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_Kummer_repair_true_background_density_feedback
    (ell a R B A c : ℝ)
    (hell : 0 < ell) (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (p q : ℂ) :
    let U : ℝ → ℂ := fun y =>
      (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
    let A0 := actualHartreeKummerRepairBackgroundEnvelope ell a R B A
    let D := ‖p‖ + R * ‖q‖
    let P := actualKummerRepairDensityPolynomial A0 D
    let F := actualKummerPhysicalRepairOuterDensityDifference U a R p q
    Integrable F ∧
    (∫ y in Ioi (a * R), |F y|) ≤ (a * R) * P ∧
    |radialHartreeExteriorCenter F (a * R)| ≤
      (4 * Real.pi * hartreeKappa) * ((a * R) * P) ∧
    ∀ r : ℝ, 0 < r → 2 * r ≤ a * R →
      |radialHartreeExteriorPotential F (a * R) r -
          radialHartreeExteriorCenter F (a * R)| ≤
        (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / (a * R))) * P := by
  dsimp only
  let U : ℝ → ℂ := fun y =>
    (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
  let A0 : ℝ := actualHartreeKummerRepairBackgroundEnvelope ell a R B A
  let D : ℝ := ‖p‖ + R * ‖q‖
  let P : ℝ := actualKummerRepairDensityPolynomial A0 D
  let F : ℝ → ℝ :=
    actualKummerPhysicalRepairOuterDensityDifference U a R p q
  have hCoreMeas :
      Measurable (fun y : ℝ => (actualMomentLockedCore c y : ℂ)) := by
    change Measurable
      (fun y : ℝ =>
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c y : ℂ))
    exact Complex.continuous_ofReal.measurable.comp
      (actual_Hartree_moving_monopole_measurable c)
  have hRadMeas : Measurable (rescalePhysicalRadiation ell z) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hUmeas : Measurable U := by
    dsimp [U]
    exact hCoreMeas.add hRadMeas
  have hA0 : 0 ≤ A0 := by
    dsimp [A0]
    exact actual_Hartree_Kummer_repair_background_envelope_nonneg
      ell a R B A hell ha hR hB hA
  have hUShell :
      ∀ y ∈ Ioc (a * R) (2 * a * R), ‖U y‖ ≤ A0 := by
    intro y hy
    dsimp [U, A0]
    exact actual_Hartree_Kummer_repair_background_shell_envelope
      ell a R B A c y hell ha hR hB hA hc z hSup hStrauss hy
  have hL1 :=
    actual_Kummer_physical_repair_outer_density_difference_L1
      U hUmeas a R A0 ha hR hA0 p q hUShell
  have hCenter :=
    actual_Kummer_physical_repair_outer_density_center_bound
      U hUmeas a R A0 ha hR hA0 p q hUShell
  refine ⟨hL1.1, ?_, ?_, ?_⟩
  · simpa only [F, P, D] using hL1.2
  · simpa only [F, P, D] using hCenter
  · intro r hr hsep
    have hGap :=
      actual_Kummer_physical_repair_outer_density_core_gap
        U hUmeas a R A0 r ha hR hA0 hr hsep p q hUShell
    simpa only [F, P, D] using hGap

end HBL.TypeIIDynamicSelection
