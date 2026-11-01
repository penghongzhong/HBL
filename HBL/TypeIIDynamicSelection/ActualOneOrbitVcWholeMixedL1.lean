import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedQuartic
import HBL.MonopoleCoreIntegrability
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# The ENTIRE actual mixed quartic source is L1 with positive half-order gain

Unlike the real-linear-only centre, this result includes all quadratic
and cubic cross interactions in the true nonlocal density

  |V_c + Z_ell|^4 - |V_c|^4 - |Z_ell|^4.

No L1 bound is a premise: it is derived from the actual chosen nonzero
annular physical terminal data, the previously proved whole-source
pointwise estimate, and the true rescaled support length.

The bound is explicit for arbitrary ell>0. Its slowest contribution
is 15 B ell sqrt(ell) = O(ell^(3/2)), a positive half-order gain
over the true radiation self-centre O(ell). This is not yet a time-
dependent PDE/Fredholm/Kummer three-region matched proof of 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact physically derived finite L1 envelope, no assumed
residual-order declaration. -/
def actualOneOrbitVcWholeMixedL1Envelope (ell : ℝ) : ℝ :=
  15 * actualOneOrbitMovingEnvelope ^ 3 * ell ^ 2 * Real.sqrt ell +
    (45 / 2 : ℝ) * actualOneOrbitMovingEnvelope ^ 2 * ell ^ 2 +
    15 * actualOneOrbitMovingEnvelope * ell * Real.sqrt ell

/-- Measurability of the genuine complete mixed density follows
from the real moment-generated moving monopole and actual smooth
complex terminal radiation, without a source interface. -/
theorem actual_one_orbit_Vc_whole_mixed_measurable
    (ell : ℝ) :
    Measurable (actualOneOrbitVcWholeMixedQuartic ell) := by
  have hv : Measurable (actualOneOrbitMovingMonopole ell) := by
    unfold actualOneOrbitMovingMonopole
    exact monopoleMovingCutoffProfile_measurable.comp
      (measurable_const.prodMk measurable_id)
  have hvC : Measurable
      (fun r : ℝ => (actualOneOrbitMovingMonopole ell r : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hv
  have hg : Continuous actualOneOrbitTerminalRadiation :=
    Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous
  have hz : Measurable
      (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hg.measurable.comp (measurable_const.mul measurable_id))
  unfold actualOneOrbitVcWholeMixedQuartic
    actualWholeRadiationMixedQuartic
  exact (((hvC.add hz).norm.pow_const 4).sub
    (hvC.norm.pow_const 4)).sub (hz.norm.pow_const 4)

/-- Complete physical quartic source: not just the first real-linear
term. This establishes absolute L1 integrability from primitive
pointwise bounds; and therefore bounds its ACTUAL Hartree centre.

The highest-order-in-Z cross term dominates and yields O(ell^(3/2))
as ell tends to zero, without postulating a blowup time exponent. -/
theorem actual_one_orbit_Vc_whole_mixed_Hartree_L1_center_gain
    (ell : ℝ) (hell : 0 < ell) :
    Integrable (actualOneOrbitVcWholeMixedQuartic ell) ∧
    (∫ r in Ioi (0 : ℝ),
      |actualOneOrbitVcWholeMixedQuartic ell r|) ≤
        actualOneOrbitVcWholeMixedL1Envelope ell ∧
    |radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      4 * Real.pi * hartreeKappa *
        actualOneOrbitVcWholeMixedL1Envelope ell := by
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let C : ℝ :=
    4 * actualOneOrbitMovingEnvelope ^ 3 *
        ell ^ 3 * Real.sqrt ell +
      6 * actualOneOrbitMovingEnvelope ^ 2 * ell ^ 3 +
      4 * actualOneOrbitMovingEnvelope * ell ^ 2 * Real.sqrt ell
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply (div_le_div_iff₀ (by positivity) hell).2
    nlinarith [hell]
  have hsupp : Function.support F ⊆ Icc a b := by
    simpa only [F, a, b] using
      actual_one_orbit_Vc_whole_mixed_support ell hell
  have hcomp : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hmeas : Measurable F :=
    actual_one_orbit_Vc_whole_mixed_measurable ell
  have hC : 0 ≤ C := by
    dsimp [C]
    have hB := actual_one_orbit_moving_envelope_pos
    positivity
  have hpoint : ∀ r ∈ Icc a b, ‖F r‖ ≤ C := by
    intro r hr
    have hrpos : 0 < r := ha.trans_le hr.1
    simpa only [F, C, Real.norm_eq_abs] using
      actual_one_orbit_Vc_whole_mixed_pointwise_gain
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
  have hEqAbs :
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
    have hNorm' :
        abs (∫ r in Icc a b, |F r|) ≤ C * (b - a) := by
      simpa only [Real.norm_eq_abs, Real.volume_real_Icc_of_le hab] using hNorm
    exact (le_abs_self _).trans hNorm'
  have hLength : C * (b - a) =
      actualOneOrbitVcWholeMixedL1Envelope ell := by
    dsimp [C, a, b, actualOneOrbitVcWholeMixedL1Envelope]
    field_simp [ne_of_gt hell]
    ring
  have hL1 : (∫ r in Ioi (0 : ℝ), |F r|) ≤
      actualOneOrbitVcWholeMixedL1Envelope ell := by
    rw [hEqAbs]
    exact hIcc.trans_eq hLength
  have hκ : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hCenter :
      |radialHartreeCenter F| ≤
        4 * Real.pi * hartreeKappa *
          actualOneOrbitVcWholeMixedL1Envelope ell := by
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
            actualOneOrbitVcWholeMixedL1Envelope ell :=
        mul_le_mul_of_nonneg_left hL1 hκ
  exact ⟨hint, hL1, hCenter⟩

end HBL.TypeIIDynamicSelection
