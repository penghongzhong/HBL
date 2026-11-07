import HBL.TypeIIDynamicSelection.ActualKummerMovingTailTruePhysicalPDE
import Mathlib.Tactic

/-!
# Genuine moving Kummer PDE on a corrected physical Hartree background

In nonlinear finite-profile recursion, the Kummer repair is added not just
to the first monopole plus physical radiation, but to its current corrected
background V_c + Z_ell + H. Its nonlocal quartic density must therefore be
recomputed on that SAME background.

Here a pointwise physical bubble estimate for the current correction H
proves the complete Hartree radial row is integrable. The actual moving
Kummer tail then has the exact original nonlinear PDE source on this
corrected background, including all mixed core/radiation/correction terms.
There is no postulated PDE residual or extra regional inverse.

Time-decay of the new cross terms remains a further quantitative obligation.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- An actual complex radial source with a uniform bubble envelope has
the required genuine three-dimensional inverse-square Hartree row. -/
theorem actual_Hartree_quartic_row_integrable_from_bubble
    (U : ℝ → ℂ) (r C : ℝ)
    (hUmeas : Measurable U) (hr : 0 < r) (hC : 0 ≤ C)
    (hU : ∀ y : ℝ, 0 < y → ‖U y‖ ≤ C * bubble y) :
    IntegrableOn
      (fun y => y * hartreeRadialLog r y * ‖U y‖ ^ 4)
      (Ioi (0 : ℝ)) := by
  have hFmeas : Measurable (fun y => ‖U y‖ ^ 4) :=
    hUmeas.norm.pow_const 4
  have hBubblePow (y : ℝ) :
      bubble y ^ 4 ≤ bubble y ^ 2 := by
    have hb0 := bubble_nonneg y
    have hb1 := bubble_le_one y
    have hb2 : bubble y ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hb0 hb1 2
    have hb20 : 0 ≤ bubble y ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hb20 (sub_nonneg.mpr hb2)]
  have hDom (y : ℝ) (hy : 0 < y) :
      |‖U y‖ ^ 4| ≤ C ^ 4 * bubble y ^ 2 := by
    calc
      |‖U y‖ ^ 4| = ‖U y‖ ^ 4 :=
        abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)
      _ ≤ (C * bubble y) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) (hU y hy) 4
      _ = C ^ 4 * bubble y ^ 4 := by ring
      _ ≤ C ^ 4 * bubble y ^ 2 :=
        mul_le_mul_of_nonneg_left (hBubblePow y) (pow_nonneg hC 4)
  exact (radialHartreePotential_bubble_sq_domination
    (fun y => ‖U y‖ ^ 4) hFmeas
    (pow_nonneg hC 4) hDom hr).1

/-- The fully corrected actual Hartree background has a global bubble
envelope derived from the original physical radiation plus H. -/
theorem actual_Hartree_corrected_background_bubble_envelope
    (ell c y B A CH : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hy : 0 < y)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (_hCH : 0 ≤ CH)
    (z H : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hH : ∀ u : ℝ, 0 < u → ‖H u‖ ≤ CH * bubble u) :
    ‖((actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y) + H y‖ ≤
      (((2 + 9 * monopoleRadialBoundConstant) +
        (2 * (B + A)) / ell) + CH) * bubble y := by
  have hOriginal :=
    actual_Hartree_true_background_bubble_envelope
      ell c y B A hell hellOne hc hy hB hA z hSup hStrauss
  calc
    ‖((actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y) + H y‖ ≤
      ‖(actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y‖ + ‖H y‖ :=
        norm_add_le _ _
    _ ≤ ((2 + 9 * monopoleRadialBoundConstant) +
        (2 * (B + A)) / ell) * bubble y +
        CH * bubble y :=
      add_le_add hOriginal (hH y hy)
    _ = (((2 + 9 * monopoleRadialBoundConstant) +
        (2 * (B + A)) / ell) + CH) * bubble y := by ring

/-- The ORIGINAL full complex Hartree PDE source of the moving Kummer
repair against the corrected physical background V_c+Z_ell+H. The
correction's nonlinear interactions are not dropped or replaced by a
linear surrogate. Only genuine regularity and a bubble-envelope estimate
for the existing correction H are required. -/
theorem actual_Kummer_moving_repair_corrected_Hartree_core_PDE_exact
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z H : ℝ → ℝ → ℂ)
    (b omega s r B A CH : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : ContinuousAt a s) (hR : 0 < R)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hr : 0 < r) (hsep : 2 * r ≤ a s * R)
    (hz : Measurable (z (time s)))
    (hHmeas : Measurable (H s))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u →
      u * ‖z (time s) u‖ ≤ A)
    (hH : ∀ u : ℝ, 0 < u → ‖H s u‖ ≤ CH * bubble u) :
    let U : ℝ → ℝ → ℂ := fun t y =>
      (actualMomentLockedCore (c t) y : ℂ) +
        rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
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
      rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
  let M : ℝ :=
    (2 + 9 * monopoleRadialBoundConstant) +
      (2 * (B + A)) / (ell s) + CH
  have hMono : 0 ≤ monopoleRadialBoundConstant :=
    monopoleRadialBoundConstant_pos.le
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hCoreMeas :
      Measurable (fun y : ℝ => (actualMomentLockedCore (c s) y : ℂ)) := by
    change Measurable
      (fun y : ℝ =>
        (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c s)) (c s) y : ℂ))
    exact Complex.continuous_ofReal.measurable.comp
      (actual_Hartree_moving_monopole_measurable (c s))
  have hZmeas :
      Measurable (rescalePhysicalRadiation (ell s) (z (time s))) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hUmeas : Measurable (U s) :=
    (hCoreMeas.add hZmeas).add hHmeas
  have hEnvelope (y : ℝ) (hy : 0 < y) :
      ‖U s y‖ ≤ M * bubble y := by
    simpa only [U, M] using
      actual_Hartree_corrected_background_bubble_envelope
        (ell s) (c s) y B A CH hell hellOne hc hy
        hB hA hCH (z (time s)) (H s) hSup hStrauss hH
  have hRow :
      IntegrableOn
        (fun y => y * hartreeRadialLog r y * ‖U s y‖ ^ 4)
        (Ioi (0 : ℝ)) :=
    actual_Hartree_quartic_row_integrable_from_bubble
      (U s) r M hUmeas hr hM hEnvelope
  have hShell :
      ∀ y ∈ Ioc (a s * R) (2 * a s * R), ‖U s y‖ ≤ M := by
    intro y hy
    have hypos : 0 < y := (mul_pos (ha s) hR).trans hy.1
    calc
      ‖U s y‖ ≤ M * bubble y := hEnvelope y hypos
      _ ≤ M * 1 :=
        mul_le_mul_of_nonneg_left (bubble_le_one y) hM
      _ = M := by ring
  exact actual_Kummer_moving_repair_true_Hartree_core_PDE_source_exact
    a R p q U b omega s r M ha haCont hR hM
    hr hsep hUmeas hRow hShell

end HBL.TypeIIDynamicSelection
