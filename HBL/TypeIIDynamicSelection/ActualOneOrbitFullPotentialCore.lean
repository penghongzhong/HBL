import HBL.TypeIIDynamicSelection.ActualOneOrbitFullInteractionCenter
import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedPositiveHalf
import HBL.TypeIIDynamicSelection.ExteriorSpatialGain
import Mathlib.Tactic

/-!
# Physical full Hartree potential at the selected terminal one-orbit datum

Combine genuine self-radiation and all nonlinear cross densities inside the
same radial inverse-square Hartree integral. No artificial cubic potential,
prescribed terminal rate, or assumed exterior radiation source is used.

The self centre cancels the moment-determined monopole exactly; the
remaining complete mixed centre and genuine Riesz spatial defects are
bounded by the previously proved positive half-order estimates.
This proves a true terminal core source estimate, not the off-terminal
three-region residual cancellation of manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- The actual self-radiation quartic density of the chosen terminal datum. -/
def actualOneOrbitSelfDensity (ell r : ℝ) : ℝ :=
  ‖rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r‖ ^ 4

theorem actual_one_orbit_self_density_measurable
    (ell : ℝ) :
    Measurable (actualOneOrbitSelfDensity ell) := by
  have hg : Continuous actualOneOrbitTerminalRadiation :=
    Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous
  have hZ : Continuous
      (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) := by
    unfold rescalePhysicalRadiation
    exact continuous_const.mul
      (hg.comp (continuous_const.mul continuous_id))
  unfold actualOneOrbitSelfDensity
  exact (hZ.norm.pow 4).measurable

theorem actual_one_orbit_self_density_zero_below
    (ell : ℝ) (hell : 0 < ell) {r : ℝ}
    (hbelow : r ≤ 1 / (4 * ell)) :
    actualOneOrbitSelfDensity ell r = 0 := by
  have hz :=
    actual_one_orbit_rescaled_terminal_zero_core ell r hell hbelow
  simp [actualOneOrbitSelfDensity, hz]

/-- This is proved for the actual selected radiation, including at the
two support boundaries, and is not an off-terminal support assertion. -/
theorem actual_one_orbit_self_density_support
    (ell : ℝ) (hell : 0 < ell) :
    Function.support (actualOneOrbitSelfDensity ell) ⊆
      Icc (1 / (4 * ell)) (4 / ell) := by
  intro r hr
  by_contra hn
  have hout : r < 1 / (4 * ell) ∨ 4 / ell < r := by
    simpa only [mem_Icc, not_and_or, not_le] using hn
  have hz : rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r = 0 := by
    rcases hout with hleft | hright
    · exact actual_one_orbit_rescaled_terminal_zero_core ell r hell hleft.le
    · exact actual_one_orbit_rescaled_terminal_zero_far ell r hell hright.le
  exact hr (by simp [actualOneOrbitSelfDensity, hz])

theorem actual_one_orbit_self_density_bound
    (ell : ℝ) (hell : 0 < ell) (r : ℝ) :
    |actualOneOrbitSelfDensity ell r| ≤ ell ^ 2 := by
  have hz := actual_one_orbit_terminal_rescaled_norm_le_sqrt ell r
  have hfour :
      ‖rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r‖ ^ 4 ≤
        (Real.sqrt ell) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hz 4
  have hp : (Real.sqrt ell) ^ 4 = ell ^ 2 := by
    calc
      (Real.sqrt ell) ^ 4 = ((Real.sqrt ell) ^ 2) ^ 2 := by ring
      _ = ell ^ 2 := by rw [Real.sq_sqrt hell.le]
  simpa only [actualOneOrbitSelfDensity,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) 4), hp] using hfour

/-- Genuine exterior self Hartree centre error; the leading coefficient
is the actual 3D moment-selected monopole, without an assumed charge. -/
theorem actual_one_orbit_self_Riesz_core_center_gain
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hsep : 2 * r ≤ 1 / (4 * ell)) :
    |radialHartreePotential (actualOneOrbitSelfDensity ell) r -
        actualOneOrbitMonopoleCoefficient ell| ≤
      16 * r ^ 2 * ell ^ 2 *
        actualOneOrbitMonopoleCoefficient ell := by
  let F : ℝ → ℝ := actualOneOrbitSelfDensity ell
  let a : ℝ := 1 / (4 * ell)
  have ha : 0 < a := by dsimp [a]; positivity
  have hm : Measurable F :=
    actual_one_orbit_self_density_measurable ell
  have hint : IntegrableOn F (Ioi (0 : ℝ)) := by
    exact actual_one_orbit_terminal_rescaled_self_integrable ell hell
  have hF : IntegrableOn F (Ioi a) :=
    hint.mono_set (fun rho hrho => ha.trans hrho)
  have hmask : (Ioi a).indicator F = F := by
    funext rho
    by_cases h : rho ∈ Ioi a
    · simp only [Set.indicator_of_mem h]
    · have hrho : rho ≤ a :=
        le_of_not_gt (by simpa only [mem_Ioi] using h)
      have hz := actual_one_orbit_self_density_zero_below
        ell hell (r := rho) hrho
      simp only [Set.indicator_of_notMem h]
      exact hz.symm
  have hP :
      radialHartreePotential F r =
        radialHartreeExteriorPotential F a r := by
    rw [radialHartreeExteriorPotential_eq_indicator F ha.le r]
    rw [hmask]
  have hs : Ioi a ⊆ Ioi (0 : ℝ) :=
    fun rho hrho => ha.trans hrho
  have hIntegral :
      (∫ rho in Ioi (0 : ℝ), F rho) =
        ∫ rho in Ioi a, F rho := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ), (Ioi a).indicator F rho := by
        rw [hmask]
      _ = ∫ rho in Ioi (0 : ℝ) ∩ Ioi a, F rho :=
        setIntegral_indicator measurableSet_Ioi
      _ = ∫ rho in Ioi a, F rho := by
        rw [inter_eq_right.mpr hs]
  have hC :
      radialHartreeExteriorCenter F a =
        actualOneOrbitMonopoleCoefficient ell := by
    have hc :=
      (actual_one_orbit_monopole_coefficient_eq_full_radiation_center
        ell hell).symm
    change radialHartreeCenter F =
      actualOneOrbitMonopoleCoefficient ell at hc
    unfold radialHartreeCenter at hc
    unfold radialHartreeExteriorCenter
    rw [hIntegral] at hc
    exact hc
  have hSelfNonneg (rho : ℝ) : 0 ≤ F rho := by
    dsimp [F, actualOneOrbitSelfDensity]
    positivity
  have hAbs :
      (∫ rho in Ioi a, |F rho|) =
        ∫ rho in Ioi a, F rho := by
    apply integral_congr_ae
    filter_upwards with rho
    exact abs_of_nonneg (hSelfNonneg rho)
  have hInv : 1 / a ^ 2 = 16 * ell ^ 2 := by
    dsimp [a]
    field_simp [hell.ne']
    ring
  have hCore :=
    actual_exteriorHartree_center_gap_L1_le F hm hF ha hr hsep
  calc
    |radialHartreePotential (actualOneOrbitSelfDensity ell) r -
        actualOneOrbitMonopoleCoefficient ell| =
      |radialHartreeExteriorPotential F a r -
        radialHartreeExteriorCenter F a| := by
        rw [hP, hC]
    _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / a ^ 2)) *
          ∫ rho in Ioi a, |F rho| := hCore
    _ = 16 * r ^ 2 * ell ^ 2 *
        actualOneOrbitMonopoleCoefficient ell := by
        rw [hAbs, hInv, ← hC]
        unfold radialHartreeExteriorCenter
        ring

/-- The full actual potential separates into genuine self and all
mixed quartic terms for every strictly positive observation radius.
The required Hartree rows follow from physical support and bounds. -/
theorem actual_one_orbit_full_interaction_potential_split
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r) :
    radialHartreePotential (actualOneOrbitFullInteractionDensity ell) r =
      radialHartreePotential (actualOneOrbitSelfDensity ell) r +
        radialHartreePotential (actualOneOrbitVcWholeMixedQuartic ell) r := by
  let G : ℝ → ℝ := actualOneOrbitSelfDensity ell
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  have ha : 0 < a := by dsimp [a]; positivity
  have hMeasG : Measurable G :=
    actual_one_orbit_self_density_measurable ell
  have hMeasF : Measurable F :=
    actual_one_orbit_Vc_whole_mixed_measurable ell
  have hCompG : HasCompactSupport G :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (by simpa only [G,a,b] using actual_one_orbit_self_density_support ell hell)
  have hCompF : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (by simpa only [F,a,b] using actual_one_orbit_Vc_whole_mixed_support ell hell)
  have hBoundG : ∀ rho, |G rho| ≤ ell ^ 2 :=
    actual_one_orbit_self_density_bound ell hell
  let M : ℝ :=
    4 * actualOneOrbitMovingEnvelope ^ 3 * ell ^ 3 * Real.sqrt ell +
      6 * actualOneOrbitMovingEnvelope ^ 2 * ell ^ 3 +
        4 * actualOneOrbitMovingEnvelope * ell ^ 2 * Real.sqrt ell
  have hM : 0 ≤ M := by
    dsimp [M]
    have hb := actual_one_orbit_moving_envelope_pos
    positivity
  have hSupportF :
      Function.support F ⊆ Icc a b := by
    simpa only [F,a,b] using actual_one_orbit_Vc_whole_mixed_support ell hell
  have hBoundF : ∀ rho, |F rho| ≤ M := by
    intro rho
    by_cases hx : rho ∈ Icc a b
    · have hpos : 0 < rho := ha.trans_le hx.1
      simpa only [F,M] using
        actual_one_orbit_Vc_whole_mixed_pointwise_gain ell rho hell hpos
    · have hz : F rho = 0 := by
        by_contra hn
        exact hx (hSupportF hn)
      rw [hz, abs_zero]
      exact hM
  have hGRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * G rho)
      (Ioi (0 : ℝ)) :=
    radialHartreePotential_integrable G hMeasG hCompG hBoundG hr
  have hFRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * F rho)
      (Ioi (0 : ℝ)) :=
    radialHartreePotential_integrable F hMeasF hCompF hBoundF hr
  have hDensity :
      actualOneOrbitFullInteractionDensity ell =
        fun rho => G rho + F rho := by
    funext rho
    exact actual_one_orbit_full_interaction_density_decomposition ell rho
  have hRow :
      (fun rho => rho * hartreeRadialLog r rho *
        (G rho + F rho)) =
      (fun rho => rho * hartreeRadialLog r rho * G rho) +
        (fun rho => rho * hartreeRadialLog r rho * F rho) := by
    funext rho
    simp only [Pi.add_apply]
    ring
  unfold radialHartreePotential
  rw [hDensity, hRow]
  change (2 * Real.pi * hartreeKappa / r) *
      (∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho * G rho +
          rho * hartreeRadialLog r rho * F rho) = _
  rw [integral_add hGRow hFRow]
  dsimp [G, F]
  ring

/-- A complete core bound on the ACTUAL nonlinear Hartree interaction
potential after cancellation of the leading radiation-selected monopole.
All cross terms and true Riesz geometry are retained. -/
theorem actual_one_orbit_full_Hartree_core_residual_gain
    (ell r : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1)
    (hr : 0 < r) (hsep : 2 * r ≤ 1 / (4 * ell)) :
    |radialHartreePotential (actualOneOrbitFullInteractionDensity ell) r -
        actualOneOrbitMonopoleCoefficient ell| ≤
      16 * r ^ 2 * ell ^ 2 *
        actualOneOrbitMonopoleCoefficient ell +
      (64 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          r ^ 2 * ell ^ 3 * Real.sqrt ell +
      (4 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell := by
  have hSelf :=
    actual_one_orbit_self_Riesz_core_center_gain ell r hell hr hsep
  have hMixed :=
    actual_one_orbit_Vc_whole_mixed_positive_half_order_source
      ell hell hsmall
  have hCenter := hMixed.2.1
  have hCore := hMixed.2.2 r hr hsep
  let P : ℝ :=
    radialHartreePotential (actualOneOrbitSelfDensity ell) r
  let Q : ℝ :=
    radialHartreePotential (actualOneOrbitVcWholeMixedQuartic ell) r
  let C : ℝ := actualOneOrbitMonopoleCoefficient ell
  let D : ℝ :=
    radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)
  have hP : |P - C| ≤ 16 * r ^ 2 * ell ^ 2 * C := hSelf
  have hQ : |Q - D| ≤
      (64 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          r ^ 2 * ell ^ 3 * Real.sqrt ell := hCore
  have hD : |D| ≤
      (4 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell := hCenter
  calc
    |radialHartreePotential (actualOneOrbitFullInteractionDensity ell) r -
        actualOneOrbitMonopoleCoefficient ell| =
      |(P - C) + (Q - D) + D| := by
        rw [actual_one_orbit_full_interaction_potential_split ell r hell hr]
        dsimp [P,Q,C,D]
        congr 1
        ring
    _ ≤ (|P - C| + |Q - D|) + |D| := by
      calc
        _ ≤ |(P - C) + (Q - D)| + |D| := abs_add_le _ _
        _ ≤ (|P - C| + |Q - D|) + |D| :=
          add_le_add (abs_add_le (P - C) (Q - D)) (le_refl |D|)
    _ ≤ 16 * r ^ 2 * ell ^ 2 * C +
      (64 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          r ^ 2 * ell ^ 3 * Real.sqrt ell +
      (4 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell :=
        add_le_add (add_le_add hP hQ) hD
    _ = _ := rfl

end HBL.TypeIIDynamicSelection
