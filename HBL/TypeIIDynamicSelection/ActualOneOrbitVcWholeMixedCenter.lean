import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeMixedQuartic
import HBL.MonopoleCoreIntegrability
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Genuine complete Hartree mixed quartic: absolute centre bound

F_ell = |V_c + Z_ell|^4 - |V_c|^4 - |Z_ell|^4.
The physical monopole V_c uses c = kappa_H ell m_0[g].
We keep all linear/quadratic/cubic cross terms; the dominant one
is 4 V_c Re(Z_ell) |Z_ell|^2.

For 0 < ell <= 1, the full source is O(ell^(5/2)) pointwise
on the actual rescaled annulus of length O(ell^(-1)).
Consequently its true physical L1 mass and Hartree centre gain
O(ell^(3/2)), a positive half order over the self-moment O(ell).

No original time-dependent four-region profile solve is claimed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- Explicit fixed source constant from the genuine monopole envelope. -/
def actualOneOrbitWholeMixedEnvelope : ℝ :=
  4 * actualOneOrbitMovingEnvelope ^ 3 +
    6 * actualOneOrbitMovingEnvelope ^ 2 +
      4 * actualOneOrbitMovingEnvelope

theorem actual_one_orbit_whole_mixed_envelope_nonneg :
    0 ≤ actualOneOrbitWholeMixedEnvelope := by
  have hp := actual_one_orbit_moving_envelope_pos
  unfold actualOneOrbitWholeMixedEnvelope
  positivity

/-- The full quartic mixed source, not merely its linear term,
has a genuine positive order on the rescaled terminal annulus. -/
theorem actual_one_orbit_Vc_whole_mixed_pointwise_two_five_gain
    (ell r : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) :
    |actualOneOrbitVcWholeMixedQuartic ell r| ≤
      actualOneOrbitWholeMixedEnvelope *
        ell ^ 2 * Real.sqrt ell := by
  let B := actualOneOrbitMovingEnvelope
  have hp : ell ^ 3 ≤ ell ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ell) (sub_nonneg.mpr hellOne)]
  have hsq : ell ^ 2 ≤ ell := by
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr hellOne)]
  have hSqrt : ell ≤ Real.sqrt ell := by
    calc
      ell = Real.sqrt (ell ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hell.le]
      _ ≤ Real.sqrt ell := Real.sqrt_le_sqrt hsq
  have hmul : ell ^ 3 ≤ ell ^ 2 * Real.sqrt ell := by
    calc
      ell ^ 3 = ell ^ 2 * ell := by ring
      _ ≤ ell ^ 2 * Real.sqrt ell :=
        mul_le_mul_of_nonneg_left hSqrt (sq_nonneg ell)
  have hlin :
      4 * B ^ 3 * ell ^ 3 * Real.sqrt ell ≤
        4 * B ^ 3 * ell ^ 2 * Real.sqrt ell := by
    calc
      _ = (4 * B ^ 3) * (ell ^ 3 * Real.sqrt ell) := by ring
      _ ≤ (4 * B ^ 3) * (ell ^ 2 * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg ell))
          (by dsimp [B]; positivity)
      _ = _ := by ring
  have hquad :
      6 * B ^ 2 * ell ^ 3 ≤
        6 * B ^ 2 * ell ^ 2 * Real.sqrt ell := by
    calc
      _ = (6 * B ^ 2) * ell ^ 3 := by ring
      _ ≤ (6 * B ^ 2) * (ell ^ 2 * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = _ := by ring
  calc
    |actualOneOrbitVcWholeMixedQuartic ell r| ≤
        4 * B ^ 3 * ell ^ 3 * Real.sqrt ell +
          6 * B ^ 2 * ell ^ 3 +
          4 * B * ell ^ 2 * Real.sqrt ell := by
        simpa only [B] using
          actual_one_orbit_Vc_whole_mixed_pointwise_gain ell r hell hr
    _ ≤ 4 * B ^ 3 * ell ^ 2 * Real.sqrt ell +
          6 * B ^ 2 * ell ^ 2 * Real.sqrt ell +
          4 * B * ell ^ 2 * Real.sqrt ell :=
      add_le_add (add_le_add hlin hquad) le_rfl
    _ = actualOneOrbitWholeMixedEnvelope *
          ell ^ 2 * Real.sqrt ell := by
      unfold actualOneOrbitWholeMixedEnvelope
      dsimp only [B]
      ring

/-- The same complete source is a *measurable* physical density,
using the actual moving monopole profile and smooth terminal datum. -/
theorem actual_one_orbit_Vc_whole_mixed_measurable
    (ell : ℝ) :
    Measurable (actualOneOrbitVcWholeMixedQuartic ell) := by
  have hv : Measurable (actualOneOrbitMovingMonopole ell) := by
    unfold actualOneOrbitMovingMonopole
    exact monopoleMovingCutoffProfile_measurable.comp
      (measurable_const.prodMk measurable_id)
  have hg : Measurable actualOneOrbitTerminalRadiation :=
    (Complex.continuous_ofReal.comp
      actual_one_orbit_terminal_bump_smooth.continuous).measurable
  have hz : Measurable
      (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hg.comp (measurable_const.mul measurable_id))
  unfold actualOneOrbitVcWholeMixedQuartic
    actualWholeRadiationMixedQuartic
  fun_prop

/-- The actual full mixed Hartree density has an absolutely convergent
physical half-line integral and an O(ell^(3/2)) centre charge. All
integrability and L1 estimates are derived from physical support,
the exact quartic expansion, and the weighted monopole profile.

The 0 < ell <= 1 condition is only the small-length regime; no
blowup exponent or time asymptotic is a premise. -/
theorem actual_one_orbit_Vc_whole_mixed_L1_center_positive_half_gain
    (ell : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1) :
    Integrable (actualOneOrbitVcWholeMixedQuartic ell) ∧
    (∫ r in Ioi (0 : ℝ), |actualOneOrbitVcWholeMixedQuartic ell r|) ≤
      (15 / 4 : ℝ) * actualOneOrbitWholeMixedEnvelope *
        ell * Real.sqrt ell ∧
    |radialHartreeCenter (actualOneOrbitVcWholeMixedQuartic ell)| ≤
      (15 * Real.pi * hartreeKappa *
        actualOneOrbitWholeMixedEnvelope) * ell * Real.sqrt ell := by
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let C : ℝ := actualOneOrbitWholeMixedEnvelope
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
  have hC : 0 ≤ C := actual_one_orbit_whole_mixed_envelope_nonneg
  have hpoint : ∀ r ∈ Icc a b,
      ‖F r‖ ≤ C * ell ^ 2 * Real.sqrt ell := by
    intro r hr
    have hrpos : 0 < r := ha.trans_le hr.1
    simpa only [F, C, Real.norm_eq_abs] using
      actual_one_orbit_Vc_whole_mixed_pointwise_two_five_gain
        ell r hell hellOne hrpos
  have hbound : ∀ r : ℝ,
      ‖F r‖ ≤ C * ell ^ 2 * Real.sqrt ell := by
    intro r
    by_cases hr : r ∈ Icc a b
    · exact hpoint r hr
    · have hz : F r = 0 := by
        by_contra hn
        exact hr (hsupp hn)
      rw [hz, norm_zero]
      positivity
  have hLp : MemLp F 1 (volume : Measure ℝ) :=
    hcomp.memLp_of_bound hmeas.aestronglyMeasurable
      (C * ell ^ 2 * Real.sqrt ell)
      (Filter.Eventually.of_forall hbound)
  have hint : Integrable F :=
    memLp_one_iff_integrable.mp hLp
  have hsuppAbs : Function.support (fun r => |F r|) ⊆ Icc a b := by
    intro r hr
    apply hsupp
    intro hz
    exact hr (by simp [hz])
  have hsuppPos : Function.support (fun r => |F r|) ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact ha.trans_le (hsuppAbs hr).1
  have heqAbs :
      (∫ r in Ioi (0 : ℝ), |F r|) =
        ∫ r in Icc a b, |F r| := by
    calc
      _ = ∫ r : ℝ, (Ioi (0 : ℝ)).indicator (fun r => |F r|) r :=
        (integral_indicator measurableSet_Ioi).symm
      _ = ∫ r : ℝ, |F r| := by
        rw [indicator_eq_self.2 hsuppPos]
      _ = ∫ r : ℝ, (Icc a b).indicator (fun r => |F r|) r := by
        rw [indicator_eq_self.2 hsuppAbs]
      _ = _ := integral_indicator measurableSet_Icc
  have hfinite : (volume : Measure ℝ) (Icc a b) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hIcc :
      (∫ r in Icc a b, |F r|) ≤
        (C * ell ^ 2 * Real.sqrt ell) * (b - a) := by
    have hpointAbs : ∀ᵐ r : ℝ ∂volume,
        r ∈ Icc a b →
          ‖|F r|‖ ≤ C * ell ^ 2 * Real.sqrt ell :=
      Filter.Eventually.of_forall (fun r hr => by
        simpa only [Real.norm_eq_abs, abs_abs] using hpoint r hr)
    have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
      (μ := volume) (s := Icc a b) (f := fun r => |F r|)
      (C := C * ell ^ 2 * Real.sqrt ell) hfinite hpointAbs
    have hNorm' : abs (∫ r in Icc a b, |F r|) ≤
        (C * ell ^ 2 * Real.sqrt ell) * (b - a) := by
      simpa only [Real.norm_eq_abs, Real.volume_real_Icc_of_le hab] using hNorm
    exact (le_abs_self _).trans hNorm'
  have hlength :
      (C * ell ^ 2 * Real.sqrt ell) * (b - a) =
        (15 / 4 : ℝ) * C * ell * Real.sqrt ell := by
    dsimp [a, b]
    field_simp [hell.ne']
    ring
  have hL1 :
      (∫ r in Ioi (0 : ℝ), |F r|) ≤
        (15 / 4 : ℝ) * C * ell * Real.sqrt ell := by
    rw [heqAbs]
    exact hIcc.trans_eq hlength
  have hκ : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hCenter :
      |radialHartreeCenter F| ≤
        (15 * Real.pi * hartreeKappa * C) *
          ell * Real.sqrt ell := by
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
            ((15 / 4 : ℝ) * C * ell * Real.sqrt ell) :=
        mul_le_mul_of_nonneg_left hL1 hκ
      _ = _ := by ring
  exact ⟨hint, hL1, hCenter⟩

end HBL.TypeIIDynamicSelection
