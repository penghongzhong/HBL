import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedPositiveHalf
import HBL.TypeIIDynamicSelection.ActualOneOrbitMovingMonopoleMixed
import Mathlib.Tactic

/-!
# Genuine Hartree monopole cancellation with complete quartic interaction

The slow monopole coefficient is fixed by the *actual* whole-radiation
self-Hartree charge. The complete interaction with the moment-selected
monopole has a real-linear, quadratic and cubic mixed density.
Here we prove that the discrepancy between the entire physical
cross-Hartree centre and the selected coefficient is exactly the
mixed quartic centre, and thus O(ell^(3/2)).

This is the true leading-centre cancellation needed by the one-orbit
source in original 2.12, NOT an assumption fixing the final rate.
Off-terminal time weights and the complete three-region PDE solver
remain to be established.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The full physical quartic density INCREMENT from adding the
genuine nonzero terminal radiation to the moment-selected monopole. -/
def actualOneOrbitFullInteractionDensity (ell r : ℝ) : ℝ :=
  let V := actualOneOrbitMovingMonopole ell r
  let Z := rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r
  ‖(V : ℂ) + Z‖ ^ 4 - ‖(V : ℂ)‖ ^ 4

/-- The total physical Hartree charge output by the complete
nonlinear quartic interaction, not a freely assigned scalar. -/
def actualOneOrbitFullInteractionCenter (ell : ℝ) : ℝ :=
  radialHartreeCenter (actualOneOrbitFullInteractionDensity ell)

/-- Pointwise exact nonlinear decomposition of the complete Hartree
interaction density into genuine self radiation and mixed terms. -/
theorem actual_one_orbit_full_interaction_density_decomposition
    (ell r : ℝ) :
    actualOneOrbitFullInteractionDensity ell r =
      ‖rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r‖ ^ 4 +
        actualOneOrbitVcWholeMixedQuartic ell r := by
  unfold actualOneOrbitFullInteractionDensity
    actualOneOrbitVcWholeMixedQuartic actualWholeRadiationMixedQuartic
  ring

/-- The exact rescaled terminal self-Hartree density is integrable,
from its ACTUAL smooth annular support. Neither source mass nor
decay is postulated. -/
theorem actual_one_orbit_terminal_rescaled_self_integrable
    (ell : ℝ) (hell : 0 < ell) :
    IntegrableOn
      (fun r : ℝ =>
        ‖rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r‖ ^ 4)
      (Ioi (0 : ℝ)) := by
  let Z : ℝ → ℂ :=
    rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation
  let G : ℝ → ℝ := fun r => ‖Z r‖ ^ 4
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  have hg : Continuous actualOneOrbitTerminalRadiation :=
    Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous
  have hZ : Continuous Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact continuous_const.mul
      (hg.comp (continuous_const.mul continuous_id))
  have hG : Continuous G := hZ.norm.pow 4
  have hsupp : Function.support G ⊆ Icc a b := by
    intro r hr
    by_contra hn
    have hout : r < a ∨ b < r := by
      simpa only [mem_Icc, not_and_or, not_le] using hn
    have hz : Z r = 0 := by
      rcases hout with hl | hh
      · exact actual_one_orbit_rescaled_terminal_zero_core
          ell r hell hl.le
      · exact actual_one_orbit_rescaled_terminal_zero_far
          ell r hell hh.le
    have hGzero : G r = 0 := by simp [G, hz]
    exact hr hGzero
  have hCompact : HasCompactSupport G :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hInt : Integrable G :=
    hG.integrable_of_hasCompactSupport hCompact
  exact hInt.integrableOn

/-- The true complete nonlinear Hartree centre splits into
the exactly selected self charge plus the mixed Hartree centre.
This is an identity in the ORIGINAL full radial inverse-square
Hartree integral, with integrability of both terms proved. -/
theorem actual_one_orbit_full_interaction_center_eq_selected_plus_mixed
    (ell : ℝ) (hell : 0 < ell) :
    actualOneOrbitFullInteractionCenter ell =
      actualOneOrbitMonopoleCoefficient ell +
        radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell) := by
  let Z : ℝ → ℂ :=
    rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation
  let G : ℝ → ℝ := fun r => ‖Z r‖ ^ 4
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  have hG : IntegrableOn G (Ioi (0 : ℝ)) := by
    exact actual_one_orbit_terminal_rescaled_self_integrable ell hell
  have hF : IntegrableOn F (Ioi (0 : ℝ)) :=
    (actual_one_orbit_Vc_whole_mixed_Hartree_L1_center_gain ell hell).1.integrableOn
  have hEq : actualOneOrbitFullInteractionDensity ell =
      fun r => G r + F r := by
    funext r
    exact actual_one_orbit_full_interaction_density_decomposition ell r
  have hSplit :
      actualOneOrbitFullInteractionCenter ell =
        actualRadiationCenter Z + radialHartreeCenter F := by
    change radialHartreeCenter (actualOneOrbitFullInteractionDensity ell) =
      actualRadiationCenter Z + radialHartreeCenter F
    rw [hEq]
    unfold radialHartreeCenter actualRadiationCenter
    rw [integral_add hG hF]
    ring
  rw [hSplit]
  rw [← actual_one_orbit_monopole_coefficient_eq_full_radiation_center
    ell hell]

/-- The COMPLETE nonlinear Hartree interaction has an actual positive
half-order residual centre after the physical slow coefficient cancels
the leading radiation self-charge. No independent smallness of the
full nonlinear density is assumed. -/
theorem actual_one_orbit_full_interaction_center_half_order_defect
    (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1) :
    |actualOneOrbitFullInteractionCenter ell -
        actualOneOrbitMonopoleCoefficient ell| ≤
      (4 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell := by
  have hMixed :=
    (actual_one_orbit_Vc_whole_mixed_positive_half_order_source
      ell hell hsmall).2.1
  calc
    _ = |radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)| := by
      rw [actual_one_orbit_full_interaction_center_eq_selected_plus_mixed ell hell]
      congr 1
      ring
    _ ≤ (4 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell := hMixed

end HBL.TypeIIDynamicSelection
