import HBL.TypeIIDynamicSelection.ActualKummerMovingTailTruePDEResidual
import HBL.TypeIIDynamicSelection.ActualKummerRepairBackgroundEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalCorrectionNextLayer
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Original Hartree PDE: no assumed spatial row for the actual Kummer tail

The background is the SAME physical moving monopole plus the genuine
critically rescaled Hartree radiation. The real nonlocal quartic-density
row integrability is derived from the global radial Strauss and monopole
envelopes, rather than postulated at the moving interface.

Consequently the full Hartree PDE residual caused by the moving Kummer
replacement tail is identified on the inner core with the ACTUAL exterior
density feedback. This is a physical source producer, not yet the full
three-region finite parametrix.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The real Hartree background V_c + Z_ell has a globally controlled
bubble envelope. The 1/ell constant is deliberately retained rather than
pretending a positive time gain in an arbitrary exterior radial row. -/
theorem actual_Hartree_true_background_bubble_envelope
    (ell c y B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hy : 0 < y)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    ‖(actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y‖ ≤
      ((2 + 9 * monopoleRadialBoundConstant) +
        (2 * (B + A)) / ell) * bubble y := by
  let Cm : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let Cr : ℝ := 2 * (B + A)
  have hCm : 0 ≤ Cm := by
    dsimp [Cm]
    have hm := monopoleRadialBoundConstant_pos.le
    positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hV :
      ‖(actualMomentLockedCore c y : ℂ)‖ ≤ Cm * bubble y := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa only [Cm] using
      actual_Hartree_moment_locked_core_bubble_envelope c y hy hc
  have hGeom : Real.sqrt (1 + y ^ 2) ≤ 1 + y := by
    calc
      _ ≤ Real.sqrt ((1 + y) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [hy.le])
      _ = 1 + y := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith)]
  have hSqrt : 0 < Real.sqrt (1 + y ^ 2) := by
    exact Real.sqrt_pos.mpr (by positivity)
  have hRel : ell * Real.sqrt (1 + y ^ 2) ≤ 1 + ell * y := by
    have hh := mul_le_mul_of_nonneg_left hGeom hell.le
    linarith only [hh, hellOne]
  have hZraw :=
    actual_Hartree_scaled_Strauss_global_radial_decay
      ell y B A hell hy hB hA z hSup hStrauss
  have hsqrtOne : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hZden :
      (ell * Real.sqrt (1 + y ^ 2)) *
          ‖rescalePhysicalRadiation ell z y‖ ≤ Cr := by
    calc
      _ ≤ (1 + ell * y) * ‖rescalePhysicalRadiation ell z y‖ :=
        mul_le_mul_of_nonneg_right hRel (norm_nonneg _)
      _ ≤ Cr * Real.sqrt ell := by simpa only [Cr] using hZraw
      _ ≤ Cr * 1 := mul_le_mul_of_nonneg_left hsqrtOne hCr
      _ = Cr := by ring
  have hZ :
      ‖rescalePhysicalRadiation ell z y‖ ≤
        (Cr / ell) * bubble y := by
    have hMult :
        ‖rescalePhysicalRadiation ell z y‖ *
          Real.sqrt (1 + y ^ 2) ≤ Cr / ell := by
      apply (le_div_iff₀ hell).2
      calc
        ‖rescalePhysicalRadiation ell z y‖ *
            Real.sqrt (1 + y ^ 2) * ell =
          (ell * Real.sqrt (1 + y ^ 2)) *
            ‖rescalePhysicalRadiation ell z y‖ := by ring
        _ ≤ Cr := hZden
    calc
      _ ≤ (Cr / ell) / Real.sqrt (1 + y ^ 2) :=
        (le_div_iff₀ hSqrt).2 hMult
      _ = (Cr / ell) * bubble y := by
        unfold bubble
        rw [div_eq_mul_inv]
  calc
    ‖(actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y‖ ≤
      ‖(actualMomentLockedCore c y : ℂ)‖ +
        ‖rescalePhysicalRadiation ell z y‖ := norm_add_le _ _
    _ ≤ Cm * bubble y + (Cr / ell) * bubble y :=
      add_le_add hV hZ
    _ = ((2 + 9 * monopoleRadialBoundConstant) +
          (2 * (B + A)) / ell) * bubble y := by
      dsimp [Cm, Cr]
      ring

/-- Actual 3D quartic Hartree background source is row-integrable at
every positive core radius. The proof uses one bona fide bubble-squared
domination, including the full radiation without compact support. -/
theorem actual_Hartree_true_background_quartic_row_integrable
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hr : 0 < r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let U : ℝ → ℂ := fun y =>
      (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
    IntegrableOn
      (fun y => y * hartreeRadialLog r y * ‖U y‖ ^ 4)
      (Ioi (0 : ℝ)) := by
  dsimp only
  let U : ℝ → ℂ := fun y =>
    (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
  let C : ℝ := (2 + 9 * monopoleRadialBoundConstant) +
    (2 * (B + A)) / ell
  have hC : 0 ≤ C := by
    dsimp [C]
    have hm := monopoleRadialBoundConstant_pos.le
    positivity
  have hCoreMeas :
      Measurable (fun y : ℝ => (actualMomentLockedCore c y : ℂ)) := by
    change Measurable
      (fun y : ℝ =>
        (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius c) c y : ℂ))
    exact Complex.continuous_ofReal.measurable.comp
      (actual_Hartree_moving_monopole_measurable c)
  have hZmeas : Measurable (rescalePhysicalRadiation ell z) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hUmeas : Measurable U := hCoreMeas.add hZmeas
  have hFmeas : Measurable (fun y => ‖U y‖ ^ 4) :=
    hUmeas.norm.pow_const 4
  have hBubblePow (y : ℝ) :
      bubble y ^ 4 ≤ bubble y ^ 2 := by
    have hb0 := bubble_nonneg y
    have hb1 := bubble_le_one y
    have hb2 : bubble y ^ 2 ≤ 1 :=
      pow_le_pow_left₀ hb0 hb1 2
    have hb20 : 0 ≤ bubble y ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hb20 (sub_nonneg.mpr hb2)]
  have hDom (y : ℝ) (hy : 0 < y) :
      |‖U y‖ ^ 4| ≤ C ^ 4 * bubble y ^ 2 := by
    have hBound :=
      actual_Hartree_true_background_bubble_envelope
        ell c y B A hell hellOne hc hy hB hA z hSup hStrauss
    have hU : ‖U y‖ ≤ C * bubble y := by
      simpa only [U, C] using hBound
    calc
      |‖U y‖ ^ 4| = ‖U y‖ ^ 4 :=
        abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)
      _ ≤ (C * bubble y) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) hU 4
      _ = C ^ 4 * bubble y ^ 4 := by ring
      _ ≤ C ^ 4 * bubble y ^ 2 :=
        mul_le_mul_of_nonneg_left (hBubblePow y)
          (pow_nonneg hC 4)
  have hRow :=
    radialHartreePotential_bubble_sq_domination
      (fun y => ‖U y‖ ^ 4) hFmeas
      (pow_nonneg hC 4) hDom hr
  exact hRow.1

/-- For the actual monopole and full 3D regular radiation there is NO
independent full-row or annular-background assumption in the physical
moving-Kummer-tail Hartree PDE source identity. -/
theorem actual_Kummer_moving_tail_actual_Hartree_core_PDE_source_exact
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z : ℝ → ℝ → ℂ)
    (b omega s r B A : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : ContinuousAt a s) (hR : 0 < R)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hr : 0 < r) (hsep : 2 * r ≤ a s * R)
    (hz : Measurable (z (time s)))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A) :
    let U : ℝ → ℝ → ℂ := fun t y =>
      (actualMomentLockedCore (c t) y : ℂ) +
        rescalePhysicalRadiation (ell t) (z (time t)) y
    complexRadialRenormalizedResidual
        (fun t y => U t y + actualKummerPhysicalOuterRepair a R p q t y)
        b omega s r -
      complexRadialRenormalizedResidual U b omega s r =
      (radialHartreeExteriorPotential
        (actualKummerPhysicalRepairOuterDensityDifference
          (U s) (a s) R (p s) (q s)) (a s * R) r : ℂ) *
          actualWholeRadiationLocalCubic (U s) r := by
  dsimp only
  let U : ℝ → ℝ → ℂ := fun t y =>
    (actualMomentLockedCore (c t) y : ℂ) +
      rescalePhysicalRadiation (ell t) (z (time t)) y
  let M : ℝ :=
    actualHartreeKummerRepairBackgroundEnvelope (ell s) (a s) R B A
  have hM : 0 ≤ M := by
    dsimp [M]
    exact actual_Hartree_Kummer_repair_background_envelope_nonneg
      (ell s) (a s) R B A hell (ha s) hR hB hA
  have hRow :
      IntegrableOn
        (fun y => y * hartreeRadialLog r y * ‖U s y‖ ^ 4)
        (Ioi (0 : ℝ)) := by
    exact actual_Hartree_true_background_quartic_row_integrable
      (ell s) (c s) r B A hell hellOne hc hr
      hB hA (z (time s)) hz hSup hStrauss
  have hCoreMeas :
      Measurable (fun y : ℝ => (actualMomentLockedCore (c s) y : ℂ)) := by
    change Measurable (fun y : ℝ =>
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s) y : ℂ))
    exact Complex.continuous_ofReal.measurable.comp
      (actual_Hartree_moving_monopole_measurable (c s))
  have hZmeas : Measurable
      (rescalePhysicalRadiation (ell s) (z (time s))) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hMeas : Measurable (U s) := hCoreMeas.add hZmeas
  have hUShell :
      ∀ y ∈ Ioc (a s * R) (2 * a s * R), ‖U s y‖ ≤ M := by
    intro y hy
    exact actual_Hartree_Kummer_repair_background_shell_envelope
      (ell s) (a s) R B A (c s) y
      hell (ha s) hR hB hA hc
      (z (time s)) hSup hStrauss hy
  exact actual_Kummer_moving_repair_true_Hartree_core_PDE_source_exact
    a R p q U b omega s r M ha haCont hR hM hr hsep
    hMeas hRow hUShell

end HBL.TypeIIDynamicSelection
