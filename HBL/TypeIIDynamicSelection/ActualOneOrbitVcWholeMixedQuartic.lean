import HBL.TypeIIDynamicSelection.ActualOneOrbitMovingMonopoleMixed
import HBL.TypeIIDynamicSelection.ActualMixedQuarticGain
import Mathlib.Tactic

/-!
# Complete mixed inverse-square Hartree quartic density on physical V_c

The ACTUAL mixed density is |V_c+Z_ell|^4 - |V_c|^4 - |Z_ell|^4,
with c=kappa_H ell m0[g] derived from a nonzero smooth terminal datum.

The exact genuine quartic expansion is reused, including *all* real-linear,
quadratic and cubic bubble/radiation interactions. The cubic-cross
term has pointwise size O(ell^(5/2)), which dominates the linear
O(ell^(7/2)) term on the remote physical radiation annulus.
Integration over the true O(ell^-1) support predicts O(ell^(3/2)),
a positive half-order gain beyond the genuine slow monopole O(ell).

This file supplies source bounds, NOT an original 2.12
time-dependent source solver, nor a chosen Type-II blowup exponent.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- Full genuine mixed quartic Hartree density at the physical
moment-generated monopole, with the entire terminal radiation. -/
def actualOneOrbitVcWholeMixedQuartic (ell r : ℝ) : ℝ :=
  actualWholeRadiationMixedQuartic
    (actualOneOrbitMovingMonopole ell)
    (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) r

/-- The selected nonnegative real radiation has exact norm at most
sqrt(ell), not an assumed s^-beta temporal rate. -/
theorem actual_one_orbit_terminal_rescaled_norm_le_sqrt
    (ell r : ℝ) :
    ‖rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r‖ ≤
      Real.sqrt ell := by
  have hb := actual_one_orbit_terminal_bump_unit_bound (ell * r)
  have hnorm :
      ‖rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r‖ =
        Real.sqrt ell * actualOneOrbitTerminalBump (ell * r) := by
    unfold rescalePhysicalRadiation actualOneOrbitTerminalRadiation
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg ell),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
  calc
    _ = Real.sqrt ell * actualOneOrbitTerminalBump (ell * r) := hnorm
    _ ≤ Real.sqrt ell * 1 :=
      mul_le_mul_of_nonneg_left hb.2 (Real.sqrt_nonneg ell)
    _ = _ := by ring

/-- The entire physical mixed density remains confined to the actual
critical rescaling of the fixed annular terminal radiation. -/
theorem actual_one_orbit_Vc_whole_mixed_support
    (ell : ℝ) (hell : 0 < ell) :
    Function.support (actualOneOrbitVcWholeMixedQuartic ell) ⊆
      Icc (1 / (4 * ell)) (4 / ell) := by
  intro r hr
  by_contra hn
  have hout : r < 1 / (4 * ell) ∨ 4 / ell < r := by
    simpa only [mem_Icc, not_and_or, not_le] using hn
  have hz : rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r = 0 := by
    rcases hout with hleft | hright
    · exact actual_one_orbit_rescaled_terminal_zero_core ell r hell hleft.le
    · exact actual_one_orbit_rescaled_terminal_zero_far ell r hell hright.le
  have hF : actualOneOrbitVcWholeMixedQuartic ell r = 0 := by
    simp [actualOneOrbitVcWholeMixedQuartic,
      actualWholeRadiationMixedQuartic, hz]
  exact hr hF

/-- The complete Hartree quartic interaction is quantitatively smaller
than the pure self-radiation term, with all physical quadratic/cubic
cross terms retained and no input source order.
The right-hand bound is valid for arbitrary ell>0. -/
theorem actual_one_orbit_Vc_whole_mixed_pointwise_gain
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r) :
    |actualOneOrbitVcWholeMixedQuartic ell r| ≤
      4 * actualOneOrbitMovingEnvelope ^ 3 *
        ell ^ 3 * Real.sqrt ell +
      6 * actualOneOrbitMovingEnvelope ^ 2 * ell ^ 3 +
      4 * actualOneOrbitMovingEnvelope * ell ^ 2 * Real.sqrt ell := by
  let B : ℝ := actualOneOrbitMovingEnvelope
  let V : ℝ → ℝ := actualOneOrbitMovingMonopole ell
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation
  have hBpos : 0 < B := actual_one_orbit_moving_envelope_pos
  by_cases hcore : ell * r ≤ 1 / 4
  · have hcoef : 0 < 4 * ell := by positivity
    have hcut : r ≤ 1 / (4 * ell) := by
      apply (le_div_iff₀ hcoef).2
      nlinarith [hcore]
    have hz : Z r = 0 :=
      actual_one_orbit_rescaled_terminal_zero_core ell r hell hcut
    have hzero : actualOneOrbitVcWholeMixedQuartic ell r = 0 := by
      simp [actualOneOrbitVcWholeMixedQuartic,
        actualWholeRadiationMixedQuartic, Z, hz]
    rw [hzero, abs_zero]
    dsimp [B]
    positivity
  · have hremote : 1 / 4 < ell * r := lt_of_not_ge hcore
    have hV : |V r| ≤ B * ell :=
      actual_one_orbit_moving_monopole_size_on_radiation_support
        ell r hell hr hremote
    have hZ : ‖Z r‖ ≤ Real.sqrt ell :=
      actual_one_orbit_terminal_rescaled_norm_le_sqrt ell r
    have hV2 : |V r| ^ 2 ≤ (B * ell) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hV 2
    have hZ2 : ‖Z r‖ ^ 2 ≤ (Real.sqrt ell) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hZ 2
    have hVZ : |V r| * ‖Z r‖ ≤ (B * ell) * Real.sqrt ell :=
      mul_le_mul hV hZ (norm_nonneg _) (by positivity)
    have hCoeff :
        6 * |V r| ^ 2 + 4 * |V r| * ‖Z r‖ ≤
          6 * (B * ell) ^ 2 + 4 * (B * ell) * Real.sqrt ell :=
      add_le_add
        (mul_le_mul_of_nonneg_left hV2 (by norm_num))
        (mul_le_mul_of_nonneg_left hVZ (by norm_num))
    have hHigher :
        |actualWholeRadiationMixedHigher V Z r| ≤
          6 * B ^ 2 * ell ^ 3 +
            4 * B * ell ^ 2 * Real.sqrt ell := by
      calc
        _ ≤ (6 * |V r| ^ 2 + 4 * |V r| * ‖Z r‖) *
              ‖Z r‖ ^ 2 :=
          actual_whole_radiation_mixed_higher_abs_le V Z r
        _ ≤ (6 * (B * ell) ^ 2 + 4 * (B * ell) * Real.sqrt ell) *
              (Real.sqrt ell) ^ 2 :=
          mul_le_mul hCoeff hZ2 (sq_nonneg _)
            (by positivity)
        _ = _ := by
          rw [Real.sq_sqrt hell.le]
          ring
    have hLin :
        |4 * V r ^ 3 * (Z r).re| ≤
          4 * B ^ 3 * ell ^ 3 * Real.sqrt ell := by
      simpa only [V, Z, B, actualOneOrbitMovingMixedLinear] using
        actual_one_orbit_moving_monopole_mixed_linear_seven_halves_gain
          ell r hell hr
    change |actualWholeRadiationMixedQuartic V Z r| ≤ _
    rw [actual_whole_radiation_mixed_linear_higher_exact]
    calc
      _ ≤ |4 * V r ^ 3 * (Z r).re| +
          |actualWholeRadiationMixedHigher V Z r| := abs_add_le _ _
      _ ≤ 4 * B ^ 3 * ell ^ 3 * Real.sqrt ell +
          (6 * B ^ 2 * ell ^ 3 + 4 * B * ell ^ 2 * Real.sqrt ell) :=
        add_le_add hLin hHigher
      _ = _ := by
        dsimp [B]
        ring

end HBL.TypeIIDynamicSelection
