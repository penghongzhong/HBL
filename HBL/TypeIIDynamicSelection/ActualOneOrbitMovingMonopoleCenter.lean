import HBL.TypeIIDynamicSelection.ActualOneOrbitMovingMonopoleMixed
import HBL.MonopoleCoreIntegrability
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Integrated genuine Hartree mixed source on the selected physical V_c

The background is the actual moment-generated monopole V_c, not the
stationary bubble W. The radiation is Z_ell = sqrt(ell) * g(ell*r)
with a fixed explicitly nonzero smooth annular terminal g.

We derive the full half-line L1 source bound and the true radial
inverse-square Hartree centre charge from already strict-checked
pointwise PDE-source and physical support theorems. No source
integrability, prescribed collapse exponent, or abstract right inverse
is a premise. This remains terminal-time input to manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The selected physical mixed source is supported exactly inside
the rescaled annular terminal radiation region. -/
theorem actual_one_orbit_Vc_mixed_source_support
    (ell : ℝ) (hell : 0 < ell) :
    Function.support (actualOneOrbitMovingMixedLinear ell) ⊆
      Icc (1 / (4 * ell)) (4 / ell) := by
  intro r hr
  by_contra hn
  have hout : r < 1 / (4 * ell) ∨ 4 / ell < r := by
    simpa only [mem_Icc, not_and_or, not_le] using hn
  have hz : actualOneOrbitMovingMixedLinear ell r = 0 := by
    rcases hout with hleft | hright
    · have hZ := actual_one_orbit_rescaled_terminal_zero_core
        ell r hell hleft.le
      simp [actualOneOrbitMovingMixedLinear, hZ]
    · have hZ := actual_one_orbit_rescaled_terminal_zero_far
        ell r hell hright.le
      simp [actualOneOrbitMovingMixedLinear, hZ]
  exact hr hz

/-- Measurability of the actual V_c mixed source uses the existing
global measurable moving monopole and the original smooth radiation. -/
theorem actual_one_orbit_Vc_mixed_source_measurable
    (ell : ℝ) :
    Measurable (actualOneOrbitMovingMixedLinear ell) := by
  have hv : Measurable (actualOneOrbitMovingMonopole ell) := by
    unfold actualOneOrbitMovingMonopole
    exact monopoleMovingCutoffProfile_measurable.comp
      (measurable_const.prodMk measurable_id)
  have hg : Continuous actualOneOrbitTerminalRadiation :=
    Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous
  have hZ : Measurable
      (fun r : ℝ =>
        (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation r).re) := by
    have hc : Continuous
        (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) := by
      unfold rescalePhysicalRadiation
      exact continuous_const.mul
        (hg.comp (continuous_const.mul continuous_id))
    exact (Complex.continuous_re.comp hc).measurable
  unfold actualOneOrbitMovingMixedLinear
  exact (measurable_const.mul (hv.pow_const 3)).mul hZ

/-- The complete physical radial L1 mass of the genuine V_c-Z_ell
real-linear mixed Hartree density has order ell^(5/2).
The absolute-value integral is controlled, not merely the signed
centre integral. This is the input required for the actual exterior
Riesz L1 multipole error; no abstract moment bound is assumed. -/
theorem actual_one_orbit_Vc_mixed_Hartree_center_L1_five_halves_gain
    (ell : ℝ) (hell : 0 < ell) :
    Integrable (actualOneOrbitMovingMixedLinear ell) ∧
    (∫ r in Ioi (0 : ℝ), |actualOneOrbitMovingMixedLinear ell r|) ≤
      15 * actualOneOrbitMovingEnvelope ^ 3 *
        ell ^ 2 * Real.sqrt ell ∧
    |radialHartreeCenter (actualOneOrbitMovingMixedLinear ell)| ≤
      (60 * Real.pi * hartreeKappa *
        actualOneOrbitMovingEnvelope ^ 3) *
          ell ^ 2 * Real.sqrt ell := by
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  let F : ℝ → ℝ := actualOneOrbitMovingMixedLinear ell
  let C : ℝ :=
    4 * actualOneOrbitMovingEnvelope ^ 3 *
      ell ^ 3 * Real.sqrt ell
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply (div_le_div_iff₀ (by positivity) hell).2
    nlinarith [hell]
  have hsupp : Function.support F ⊆ Icc a b := by
    simpa only [F, a, b] using
      actual_one_orbit_Vc_mixed_source_support ell hell
  have hcomp : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hmeas : Measurable F :=
    actual_one_orbit_Vc_mixed_source_measurable ell
  have hC : 0 ≤ C := by
    dsimp [C]
    have hp := actual_one_orbit_moving_envelope_pos
    positivity
  have hpoint : ∀ r ∈ Icc a b, ‖F r‖ ≤ C := by
    intro r hr
    have hrpos : 0 < r := ha.trans_le hr.1
    simpa only [F, C, Real.norm_eq_abs] using
      actual_one_orbit_moving_monopole_mixed_linear_seven_halves_gain
        ell r hell hrpos
  have hbound : ∀ r : ℝ, ‖F r‖ ≤ C := by
    intro r
    by_cases hr : r ∈ Icc a b
    · exact hpoint r hr
    · have hz : F r = 0 := by
        by_contra hne
        exact hr (hsupp hne)
      rw [hz, norm_zero]
      exact hC
  have hLp : MemLp F 1 (volume : Measure ℝ) :=
    hcomp.memLp_of_bound hmeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hint : Integrable F :=
    (memLp_one_iff_integrable).mp hLp
  have hsuppAbs : Function.support (fun r => |F r|) ⊆ Icc a b := by
    intro r hr
    apply hsupp
    intro hz
    exact hr (by simp [hz])
  have hsuppAbsPos :
      Function.support (fun r => |F r|) ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact ha.trans_le (hsuppAbs hr).1
  have heqAbs :
      (∫ r in Ioi (0 : ℝ), |F r|) =
        ∫ r in Icc a b, |F r| := by
    calc
      _ = ∫ r : ℝ, (Ioi (0 : ℝ)).indicator (fun r => |F r|) r :=
        (integral_indicator measurableSet_Ioi).symm
      _ = ∫ r : ℝ, |F r| := by
        rw [indicator_eq_self.2 hsuppAbsPos]
      _ = ∫ r : ℝ, (Icc a b).indicator (fun r => |F r|) r := by
        rw [indicator_eq_self.2 hsuppAbs]
      _ = _ := integral_indicator measurableSet_Icc
  have hfinite : (volume : Measure ℝ) (Icc a b) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hIcc :
      (∫ r in Icc a b, |F r|) ≤ C * (b - a) := by
    have hpointAbs : ∀ᵐ r : ℝ ∂volume,
        r ∈ Icc a b → ‖|F r|‖ ≤ C :=
      Filter.Eventually.of_forall (fun r hr => by
        simpa only [Real.norm_eq_abs, abs_abs] using hpoint r hr)
    have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
      (μ := volume) (s := Icc a b) (f := fun r => |F r|)
      (C := C) hfinite hpointAbs
    have hNorm' : abs (∫ r in Icc a b, |F r|) ≤ C * (b - a) := by
      simpa only [Real.norm_eq_abs, Real.volume_real_Icc_of_le hab] using hNorm
    exact (le_abs_self _).trans hNorm'
  have hlength :
      C * (b - a) =
        15 * actualOneOrbitMovingEnvelope ^ 3 *
          ell ^ 2 * Real.sqrt ell := by
    dsimp [C, a, b]
    field_simp [ne_of_gt hell]
    ring
  have hRadialAbs :
      (∫ r in Ioi (0 : ℝ), |F r|) ≤
        15 * actualOneOrbitMovingEnvelope ^ 3 *
          ell ^ 2 * Real.sqrt ell := by
    rw [heqAbs]
    exact hIcc.trans_eq hlength
  have hκ : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hCenter :
      |radialHartreeCenter F| ≤
        (60 * Real.pi * hartreeKappa *
          actualOneOrbitMovingEnvelope ^ 3) *
            ell ^ 2 * Real.sqrt ell := by
    calc
      |radialHartreeCenter F| =
          (4 * Real.pi * hartreeKappa) *
            |∫ r in Ioi (0 : ℝ), F r| := by
        unfold radialHartreeCenter
        rw [abs_mul, abs_of_nonneg hκ]
      _ ≤ (4 * Real.pi * hartreeKappa) *
            (∫ r in Ioi (0 : ℝ), |F r|) :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hκ
      _ ≤ (4 * Real.pi * hartreeKappa) *
            (15 * actualOneOrbitMovingEnvelope ^ 3 *
              ell ^ 2 * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left hRadialAbs hκ
      _ = _ := by ring
  exact ⟨hint, hRadialAbs, hCenter⟩

end HBL.TypeIIDynamicSelection
