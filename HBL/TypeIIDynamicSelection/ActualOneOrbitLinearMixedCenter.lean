import HBL.TypeIIDynamicSelection.ActualOneOrbitLinearMixedGain
import Mathlib.Tactic

/-!
# Actual integrated 3D Hartree linear mixed charge from ONE selected terminal datum

The previous strict theorem shows |4 W³ Re Z_ell| <= 256 ell³ sqrt(ell)
and that the true rescaled terminal radiation vanishes outside
[1/(4ell), 4/ell]. We integrate over this ACTUAL physical support.

The resulting physical inverse-square Hartree centre charge has
a strictly positive gain 2 + 1/2 powers in the scale ell,
without prescribing any Type II blowup exponent, any abstract
generated-order label, or any artificial remote-support hypothesis.
This is a terminal-time source estimate, NOT yet the full time-dependent
three-region matched PDE one-layer elimination of manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The exact real-linear piece of the physical quartic
bubble-radiation density for the chosen nonzero annular datum. -/
def actualOneOrbitLinearMixedDensity (ell : ℝ) (r : ℝ) : ℝ :=
  4 * bubble r ^ 3 *
    (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re

/-- Exact support: the critical rescaling moves the terminal annulus
to [1/(4ell), 4/ell] without a chosen temporal blowup rate. -/
theorem actual_one_orbit_linear_mixed_density_support
    (ell : ℝ) (hell : 0 < ell) :
    Function.support (actualOneOrbitLinearMixedDensity ell) ⊆
      Icc (1 / (4 * ell)) (4 / ell) := by
  intro r hr
  by_contra hn
  have houtside :
      r < 1 / (4 * ell) ∨ 4 / ell < r := by
    simpa only [mem_Icc, not_and_or, not_le] using hn
  rcases houtside with hleft | hright
  · have hz := actual_one_orbit_rescaled_terminal_zero_core
      ell r hell hleft.le
    have hf : actualOneOrbitLinearMixedDensity ell r = 0 := by
      simp [actualOneOrbitLinearMixedDensity, hz]
    exact hr hf
  · have hz := actual_one_orbit_rescaled_terminal_zero_far
      ell r hell hright.le
    have hf : actualOneOrbitLinearMixedDensity ell r = 0 := by
      simp [actualOneOrbitLinearMixedDensity, hz]
    exact hr hf

/-- The concrete full-line source is continuous; in particular its
physical centre charge is a legitimate absolutely convergent integral. -/
theorem actual_one_orbit_linear_mixed_density_continuous
    (ell : ℝ) :
    Continuous (actualOneOrbitLinearMixedDensity ell) := by
  have hG : Continuous actualOneOrbitTerminalRadiation :=
    Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous
  have hscaled : Continuous (fun r : ℝ => ell * r) :=
    continuous_const.mul continuous_id
  have hZ : Continuous
      (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) := by
    change Continuous (fun r : ℝ =>
      (Real.sqrt ell : ℂ) * actualOneOrbitTerminalRadiation (ell * r))
    exact continuous_const.mul (hG.comp hscaled)
  have hW : Continuous bubble := bubble_contDiff_infty.continuous
  change Continuous (fun r : ℝ =>
    4 * bubble r ^ 3 *
      (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re)
  exact (continuous_const.mul (hW.pow 3)).mul
    (Complex.continuous_re.comp hZ)

/-- The TRUE radial three-dimensional inverse-square Hartree linear
mixed charge is O(ell^(5/2)) at the selected nonzero terminal datum.

The conservative constant 3840*pi*kappa_H follows directly from
the strict pointwise bound and the exact annulus length. Neither
integrability, localization, nor the claimed gain is assumed. -/
theorem actual_one_orbit_linear_mixed_Hartree_center_five_halves_gain
    (ell : ℝ) (hell : 0 < ell) :
    IntegrableOn (actualOneOrbitLinearMixedDensity ell) (Ioi (0 : ℝ)) ∧
    |radialHartreeCenter (actualOneOrbitLinearMixedDensity ell)| ≤
      (3840 * Real.pi * hartreeKappa) * ell ^ 2 * Real.sqrt ell := by
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  let F : ℝ → ℝ := actualOneOrbitLinearMixedDensity ell
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply (div_le_div_iff₀ (by positivity) hell).2
    nlinarith [hell]
  have hsupp : Function.support F ⊆ Icc a b := by
    simpa only [F, a, b] using
      actual_one_orbit_linear_mixed_density_support ell hell
  have hcomp : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hint : Integrable F :=
    (actual_one_orbit_linear_mixed_density_continuous ell)
      .integrable_of_hasCompactSupport hcomp
  have hsuppPos : Function.support F ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact ha.trans_le (hsupp hr).1
  have heq :
      (∫ r in Ioi (0 : ℝ), F r) =
        ∫ r in Icc a b, F r := by
    calc
      _ = ∫ r : ℝ, (Ioi (0 : ℝ)).indicator F r :=
        (integral_indicator measurableSet_Ioi).symm
      _ = ∫ r : ℝ, F r := by
        rw [indicator_eq_self.2 hsuppPos]
      _ = ∫ r : ℝ, (Icc a b).indicator F r := by
        rw [indicator_eq_self.2 hsupp]
      _ = _ := integral_indicator measurableSet_Icc
  have hpoint : ∀ r ∈ Icc a b,
      ‖F r‖ ≤ 256 * ell ^ 3 * Real.sqrt ell := by
    intro r hr
    have hrpos : 0 < r := ha.trans_le hr.1
    simpa only [F, actualOneOrbitLinearMixedDensity, Real.norm_eq_abs] using
      actual_one_orbit_terminal_mixed_linear_density_seven_halves_gain
        ell r hell hrpos
  have hfinite : (volume : Measure ℝ) (Icc a b) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hIcc :
      ‖∫ r in Icc a b, F r‖ ≤
        (256 * ell ^ 3 * Real.sqrt ell) * (b - a) := by
    have hbound : ∀ᵐ r : ℝ ∂volume,
        r ∈ Icc a b → ‖F r‖ ≤ 256 * ell ^ 3 * Real.sqrt ell :=
      Filter.Eventually.of_forall (fun r hr => hpoint r hr)
    have h := norm_setIntegral_le_of_norm_le_const_ae'
      (μ := volume) (s := Icc a b) (f := F)
      (C := 256 * ell ^ 3 * Real.sqrt ell) hfinite hbound
    simpa only [Real.volume_real_Icc_of_le hab] using h
  have hlength :
      (256 * ell ^ 3 * Real.sqrt ell) * (b - a) =
        960 * ell ^ 2 * Real.sqrt ell := by
    dsimp [a, b]
    field_simp [ne_of_gt hell]
    ring
  have hradial :
      |∫ r in Ioi (0 : ℝ), F r| ≤
        960 * ell ^ 2 * Real.sqrt ell := by
    rw [heq, ← Real.norm_eq_abs]
    exact hIcc.trans_eq hlength
  have hκ : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  refine ⟨hint.integrableOn, ?_⟩
  calc
    |radialHartreeCenter F| =
        (4 * Real.pi * hartreeKappa) *
          |∫ r in Ioi (0 : ℝ), F r| := by
        unfold radialHartreeCenter
        rw [abs_mul, abs_of_nonneg hκ]
    _ ≤ (4 * Real.pi * hartreeKappa) *
          (960 * ell ^ 2 * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left hradial hκ
    _ = (3840 * Real.pi * hartreeKappa) *
          ell ^ 2 * Real.sqrt ell := by ring

end HBL.TypeIIDynamicSelection
