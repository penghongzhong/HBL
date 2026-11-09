import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import Mathlib.Tactic

/-!
# Two-scale Hartree quartic density and local-cubic Taylor bounds

The genuine physical background is V_c + sqrt(ell)*z(ell*r), NOT
a field with a uniform-in-ell single-bubble pointwise envelope.
The true two radial scales 1+r and 1+ell*r stay visible in EVERY
quadratic density and cubic remainder estimate. This is the
nonlocal Riesz integration producer, not a complete time gain.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The true original quartic Hartree density and cubic multipliers admit
their full five-component first/second-order Taylor bounds with the
correct distinct physical scales. No ell^(-1/2) bubble constant occurs. -/
theorem actual_Hartree_true_two_scale_density_and_cubic_Taylor_bounds
    (ell c r B A e : ℝ)
    (hell : 0 < ell) (hr : 0 < r)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (hA : 0 ≤ A) (he : 0 ≤ e)
    (z h : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hh : ‖h r‖ ≤ e) :
    let U : ℂ :=
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r : ℂ) +
        rescalePhysicalRadiation ell z r
    let M : ℝ :=
      (2 + 9 * monopoleRadialBoundConstant) / (1 + r) +
        2 * (B + A) * Real.sqrt ell / (1 + ell * r)
    |actualHartreeComplexDensityLinear U (h r)| ≤ 4 * M ^ 3 * e ∧
    |actualHartreeComplexDensityRemainder U (h r)| ≤
      6 * M ^ 2 * e ^ 2 + 4 * M * e ^ 3 + e ^ 4 ∧
    ‖actualHartreeComplexCubic U‖ ≤ M ^ 3 ∧
    ‖actualHartreeComplexCubicLinear U (h r)‖ ≤ 3 * M ^ 2 * e ∧
    ‖actualHartreeComplexCubicRemainder U (h r)‖ ≤
      (3 * M + e) * e ^ 2 := by
  dsimp only
  let V : ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r
  let Z : ℂ := rescalePhysicalRadiation ell z r
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let U : ℂ := (V : ℂ) + Z
  let M : ℝ := D / (1 + r) + E * Real.sqrt ell / (1 + ell * r)
  have hden : 0 < 1 + r := by linarith
  have hden2 : 0 < 1 + ell * r := by
    nlinarith [mul_pos hell hr]
  have hD : 0 ≤ D := by
    dsimp [D]
    have hm := monopoleRadialBoundConstant_pos
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (div_nonneg hD hden.le)
      (div_nonneg (mul_nonneg hE (Real.sqrt_nonneg ell)) hden2.le)
  have hV :
      (1 + r) * |V| ≤ D := by
    dsimp only [V, D]
    exact actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hZ :
      (1 + ell * r) * ‖Z‖ ≤ E * Real.sqrt ell := by
    dsimp only [Z, E]
    exact actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss
  have hVamp : ‖(V : ℂ)‖ ≤ D / (1 + r) := by
    have h : |V| * (1 + r) ≤ D := by nlinarith only [hV]
    have hhV := (le_div_iff₀ hden).2 h
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hhV
  have hZamp : ‖Z‖ ≤ E * Real.sqrt ell / (1 + ell * r) := by
    have h : ‖Z‖ * (1 + ell * r) ≤ E * Real.sqrt ell := by
      nlinarith only [hZ]
    exact (le_div_iff₀ hden2).2 h
  have hUnorm : ‖U‖ ≤ M := by
    calc
      ‖U‖ = ‖(V : ℂ) + Z‖ := rfl
      _ ≤ ‖(V : ℂ)‖ + ‖Z‖ := norm_add_le _ _
      _ ≤ D / (1 + r) + E * Real.sqrt ell / (1 + ell * r) :=
        add_le_add hVamp hZamp
      _ = M := rfl
  have hPoly :=
    actual_Hartree_complex_Taylor_polynomial_bounds
      U (h r) hM he hUnorm hh
  simpa only [U, M, V, Z, D, E] using hPoly

end HBL.TypeIIDynamicSelection
