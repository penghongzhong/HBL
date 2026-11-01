import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedRieszCore
import Mathlib.Tactic

/-!
# Physical full Hartree mixed quartic: explicit positive half-order gain

For the actual moment-generated monopole V_c and the entire selected
nonzero terminal radiation, this proves the complete real-linear,
quadratic and cubic cross source and genuine Hartree Riesz-core error
have a positive 1/2 scale gain beyond the leading O(ell) radiation
self-centre. No terminal Type II exponent is prescribed.

This is strictly a terminal-time source ingredient, not the complete
time-dependent Fredholm/Kummer/remote matching in manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualOneOrbitVcWholeMixedHalfOrderCoefficient : ℝ :=
  15 * actualOneOrbitMovingEnvelope ^ 3 +
    (45 / 2 : ℝ) * actualOneOrbitMovingEnvelope ^ 2 +
      15 * actualOneOrbitMovingEnvelope

theorem actual_one_orbit_Vc_whole_mixed_half_order_coefficient_pos :
    0 < actualOneOrbitVcWholeMixedHalfOrderCoefficient := by
  have hB := actual_one_orbit_moving_envelope_pos
  unfold actualOneOrbitVcWholeMixedHalfOrderCoefficient
  positivity

/-- Actual exact L1 envelope is O(ell^(3/2)) for 0<ell<=1. -/
theorem actual_one_orbit_Vc_whole_mixed_envelope_half_order
    (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1) :
    actualOneOrbitVcWholeMixedL1Envelope ell ≤
      actualOneOrbitVcWholeMixedHalfOrderCoefficient *
        ell * Real.sqrt ell := by
  let B : ℝ := actualOneOrbitMovingEnvelope
  let k1 : ℝ := 15 * B ^ 3
  let k2 : ℝ := (45 / 2 : ℝ) * B ^ 2
  let k3 : ℝ := 15 * B
  have hB : 0 < B := actual_one_orbit_moving_envelope_pos
  have hk1 : 0 ≤ k1 := by dsimp [k1]; positivity
  have hk2 : 0 ≤ k2 := by dsimp [k2]; positivity
  have hEllSq : ell ^ 2 ≤ ell := by
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr hsmall)]
  have hEllSqrt : ell ≤ Real.sqrt ell := by
    calc
      ell = Real.sqrt (ell ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hell]
      _ ≤ Real.sqrt ell := Real.sqrt_le_sqrt hEllSq
  have h1 : ell ^ 2 * Real.sqrt ell ≤
      ell * Real.sqrt ell :=
    mul_le_mul_of_nonneg_right hEllSq (Real.sqrt_nonneg ell)
  have h2 : ell ^ 2 ≤ ell * Real.sqrt ell := by
    have h := mul_le_mul_of_nonneg_left hEllSqrt hell.le
    simpa only [pow_two] using h
  calc
    actualOneOrbitVcWholeMixedL1Envelope ell =
        k1 * (ell ^ 2 * Real.sqrt ell) +
          k2 * ell ^ 2 + k3 * (ell * Real.sqrt ell) := by
      dsimp [actualOneOrbitVcWholeMixedL1Envelope, k1, k2, k3, B]
      ring
    _ ≤ k1 * (ell * Real.sqrt ell) +
          k2 * (ell * Real.sqrt ell) +
            k3 * (ell * Real.sqrt ell) :=
      add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left h1 hk1)
          (mul_le_mul_of_nonneg_left h2 hk2))
        (le_refl _)
    _ = actualOneOrbitVcWholeMixedHalfOrderCoefficient *
          ell * Real.sqrt ell := by
      dsimp [actualOneOrbitVcWholeMixedHalfOrderCoefficient, k1, k2, k3, B]
      ring

/-- Strict positive half-order source bound for all quartic mixed terms,
and corresponding physical inverse-square Hartree core defect. -/
theorem actual_one_orbit_Vc_whole_mixed_positive_half_order_source
    (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1) :
    (∫ rho in Ioi (0 : ℝ), |actualOneOrbitVcWholeMixedQuartic ell rho|) ≤
      actualOneOrbitVcWholeMixedHalfOrderCoefficient *
        ell * Real.sqrt ell ∧
    |radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      (4 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
          ell * Real.sqrt ell ∧
    ∀ r : ℝ, 0 < r → 2 * r ≤ 1 / (4 * ell) →
      |radialHartreePotential (actualOneOrbitVcWholeMixedQuartic ell) r -
        radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)| ≤
          (64 * Real.pi * hartreeKappa *
            actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
              r ^ 2 * ell ^ 3 * Real.sqrt ell := by
  have hEnv :=
    actual_one_orbit_Vc_whole_mixed_envelope_half_order ell hell hsmall
  have hWhole :=
    actual_one_orbit_Vc_whole_mixed_Hartree_L1_center_gain ell hell
  have hκ : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hL1 :
      (∫ rho in Ioi (0 : ℝ),
        |actualOneOrbitVcWholeMixedQuartic ell rho|) ≤
        actualOneOrbitVcWholeMixedHalfOrderCoefficient *
          ell * Real.sqrt ell :=
    hWhole.2.1.trans hEnv
  have hCenter :
      |radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)| ≤
        (4 * Real.pi * hartreeKappa *
          actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
            ell * Real.sqrt ell := by
    calc
      _ ≤ 4 * Real.pi * hartreeKappa *
            actualOneOrbitVcWholeMixedL1Envelope ell := hWhole.2.2
      _ ≤ 4 * Real.pi * hartreeKappa *
            (actualOneOrbitVcWholeMixedHalfOrderCoefficient *
              ell * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left hEnv hκ
      _ = _ := by ring
  refine ⟨hL1, hCenter, ?_⟩
  intro r hr hsep
  have hR :=
    (actual_one_orbit_Vc_whole_mixed_Riesz_core_gain
      ell r hell hr hsep).2
  have hc : 0 ≤ 64 * Real.pi * hartreeKappa * r ^ 2 * ell ^ 2 := by
    unfold hartreeKappa
    positivity
  calc
    _ ≤ 64 * Real.pi * hartreeKappa * r ^ 2 * ell ^ 2 *
        actualOneOrbitVcWholeMixedL1Envelope ell := hR
    _ ≤ 64 * Real.pi * hartreeKappa * r ^ 2 * ell ^ 2 *
        (actualOneOrbitVcWholeMixedHalfOrderCoefficient *
          ell * Real.sqrt ell) :=
      mul_le_mul_of_nonneg_left hEnv hc
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
