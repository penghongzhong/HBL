import HBL.TypeIIDynamicSelection.ActualHartreeMixedRieszCubicWeighted
import HBL.TypeIIDynamicSelection.ActualHartreeRieszMeasurability
import HBL.AffineTailRationalIntegrability
import Mathlib.Tactic

/-!
# Full genuine Hartree mixed Riesz × moving-monopole cubic in the manuscript L²

The earlier physical source estimate is
 <r>^sigma |I(F_mix)(r)| |V_c(r)|^3 <= C sqrt(ell) W(r).
Here W²(r)=(1+r²)^(-1) is genuinely integrable on the positive half-line.
We derive membership in the original L^(2,sigma) Fredholm source space,
including measurability of the SAME actual logarithmic Riesz convolution.

The proof does not use compact terminal-radiation support, an assumed
generated source order or any preselected Type-II blowup rate.
The outer / normalized-Kummer C1 matching and all other source terms
remain distinct obligations for the revised original 2.13 environment.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Full mixed inverse-square Hartree Riesz × physical monopole cubic
belongs to the *original* Fredholm weighted-L² space. The positive
sqrt(ell) pointwise gain is proved by the genuine spatial kernel. -/
theorem actual_Hartree_full_mixed_Riesz_monopole_cubic_mem_weighted_L2
    (ell c B A sigma : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSigma : sigma ≤ 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    MemLp
      (fun r : ℝ =>
        affineJapaneseWeight sigma r *
          ‖(radialHartreePotential
            (actualWholeRadiationMixedQuartic
              (monopolePerturbedRadialProfile
                (monopoleQuadraticRadius c) c)
              (rescalePhysicalRadiation ell z)) r : ℂ) *
            ((monopolePerturbedRadialProfile
              (monopoleQuadraticRadius c) c r : ℂ) ^ 3)‖)
      2 halfLineMeasure := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let F : ℝ → ℝ := actualWholeRadiationMixedQuartic V Z
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let C : ℝ :=
    ((radialHartreeRowBoundConstant *
      (4 * D ^ 3 * (2 * (B + A)) +
       6 * D ^ 2 * (2 * (B + A)) ^ 2 +
       4 * D * (2 * (B + A)) ^ 3)) *
       D ^ 3) * Real.sqrt ell
  let S : ℝ → ℝ := fun r =>
    affineJapaneseWeight sigma r *
      ‖(radialHartreePotential F r : ℂ) * ((V r : ℂ) ^ 3)‖
  have hC : 0 ≤ C := by
    dsimp [C, D]
    have hmon := monopoleRadialBoundConstant_pos
    have hrow := radialHartreeRowBoundConstant_pos
    positivity
  have hB0 (r : ℝ) : 0 ≤ bubble r := by
    unfold bubble
    positivity
  have hBubbleInt : IntegrableOn
      (fun r : ℝ => bubble r ^ 2) (Ioi (0 : ℝ)) := by
    have hEq : (fun r : ℝ => bubble r ^ 2) =
        (fun r : ℝ => (1 + r ^ 2)⁻¹) := by
      funext r
      unfold bubble
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    rw [hEq]
    exact integrable_inv_one_add_sq.integrableOn
  have hBubbleMem : MemLp bubble 2 halfLineMeasure := by
    apply (memLp_two_iff_integrable_sq
      (bubble_contDiff_infty.continuous.measurable.aestronglyMeasurable.restrict)).2
    exact hBubbleInt
  have hMajor : MemLp (fun r => C * bubble r)
      2 halfLineMeasure := hBubbleMem.const_mul C
  have hV : Measurable V := by
    dsimp [V]
    exact monopoleMovingCutoffProfile_measurable.comp
      (measurable_const.prodMk measurable_id)
  have hZ : Measurable Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hVC : Measurable (fun r => (V r : ℂ)) :=
    Complex.measurable_ofReal.comp hV
  have hF : Measurable F := by
    dsimp [F, actualWholeRadiationMixedQuartic]
    exact (((hVC.add hZ).norm.pow_const 4).sub
      (hVC.norm.pow_const 4)).sub (hZ.norm.pow_const 4)
  have hP : Measurable (fun r => (radialHartreePotential F r : ℂ)) :=
    Complex.measurable_ofReal.comp
      (actual_radialHartreePotential_measurable F hF)
  have hS : Measurable S := by
    dsimp [S]
    exact (affineJapaneseWeight_continuous sigma).measurable.mul
      ((hP.mul (hVC.pow_const 3)).norm)
  have hS0 (r : ℝ) : 0 ≤ S r := by
    dsimp [S, affineJapaneseWeight]
    positivity
  have hPoint (r : ℝ) (hr : 0 < r) : S r ≤ C * bubble r := by
    have h :=
      actual_Hartree_full_mixed_Riesz_times_monopole_cubic_weighted_pointwise
        ell c r B A sigma hell hellOne hr hc hB hA
        hSigma z hz hSup hStrauss
    simpa only [S, C, D, F, V, Z, mul_assoc] using h
  have hDom : ∀ᵐ r : ℝ ∂halfLineMeasure,
      ‖S r‖ ≤ ‖C * bubble r‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hR : 0 ≤ C * bubble r := mul_nonneg hC (hB0 r)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hS0 r),
      abs_of_nonneg hR] using hPoint r hr
  change MemLp S 2 halfLineMeasure
  exact hMajor.mono' hS.aestronglyMeasurable.restrict hDom

end HBL.TypeIIDynamicSelection
