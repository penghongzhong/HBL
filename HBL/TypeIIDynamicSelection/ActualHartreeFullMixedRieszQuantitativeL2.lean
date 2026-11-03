import HBL.TypeIIDynamicSelection.ActualHartreeMixedRieszCubicWeightedLp
import HBL.AffineTailRationalIntegrability
import Mathlib.Tactic

/-!
# True positive quantitative weighted L2 gain from the full physical mixed Riesz term

The actual inverse-square Hartree quartic mixed density includes
ALL linear, quadratic and cubic cross terms. On a genuine high
regularity radial Hartree orbit its Riesz potential times the
physical moving-monopole cubic is pointwise bounded by
 C(B,A)*sqrt(ell)*bubble(r) in the ORIGINAL Fredholm weight.
We integrate that exact bound in the native half-line measure,
obtaining squared L2 norm at most C(B,A)^2*ell*int bubble^2.
No Type II rate is postulated.

This is one concrete source class in the revised 2.13 hierarchy,
NOT the entire Hartree nonlinearity (which has changed cubic
multipliers, pure-radiation components, transport and interfaces).
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A true quantitative O(sqrt ell) original Fredholm L2 source
for full mixed quartic Riesz x actual moving-monopole cubic.
No asserted source-order proxy or prescribed concentration law. -/
theorem actual_Hartree_full_mixed_Riesz_monopole_cubic_L2_square_gain
    (ell c B A sigma : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSigma : sigma ≤ 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ r in Ioi (0 : ℝ),
        (affineJapaneseWeight sigma r *
          ‖(radialHartreePotential
            (actualWholeRadiationMixedQuartic
              (monopolePerturbedRadialProfile
                (monopoleQuadraticRadius c) c)
              (rescalePhysicalRadiation ell z)) r : ℂ) *
            ((monopolePerturbedRadialProfile
              (monopoleQuadraticRadius c) c r : ℂ) ^ 3)‖) ^ 2) ≤
        C ^ 2 * ell * (∫ r in Ioi (0 : ℝ), bubble r ^ 2) := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let F : ℝ → ℝ := actualWholeRadiationMixedQuartic V Z
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let C : ℝ :=
    (radialHartreeRowBoundConstant *
      (4 * D ^ 3 * (2 * (B + A)) +
       6 * D ^ 2 * (2 * (B + A)) ^ 2 +
       4 * D * (2 * (B + A)) ^ 3)) * D ^ 3
  let S : ℝ → ℝ := fun r =>
    affineJapaneseWeight sigma r *
      ‖(radialHartreePotential F r : ℂ) * ((V r : ℂ) ^ 3)‖
  have hC : 0 ≤ C := by
    dsimp [C,D]
    have hm := monopoleRadialBoundConstant_pos
    have hr := radialHartreeRowBoundConstant_pos
    positivity
  refine ⟨C,hC,?_⟩
  have hMem : MemLp S 2 halfLineMeasure := by
    change MemLp
      (fun r : ℝ =>
        affineJapaneseWeight sigma r *
          ‖(radialHartreePotential F r : ℂ) * ((V r : ℂ) ^ 3)‖)
      2 halfLineMeasure
    exact actual_Hartree_full_mixed_Riesz_monopole_cubic_mem_weighted_L2
      ell c B A sigma hell hellOne hc hB hA hSigma
      z hz hSup hStrauss
  have hSm : AEStronglyMeasurable S halfLineMeasure :=
    hMem.aestronglyMeasurable
  have hSInt : IntegrableOn (fun r : ℝ => S r ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq hSm).1 hMem
  have hBubbleInt : IntegrableOn
      (fun r : ℝ => bubble r ^ 2) (Ioi (0 : ℝ)) := by
    have hEq : (fun r : ℝ => bubble r ^ 2) =
        (fun r : ℝ => (1 + r ^ 2)⁻¹) := by
      funext r
      unfold bubble
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    rw [hEq]
    exact integrable_inv_one_add_sq.integrableOn
  have hMajorInt : IntegrableOn
      (fun r : ℝ => (C * Real.sqrt ell) ^ 2 * bubble r ^ 2)
      (Ioi (0 : ℝ)) :=
    hBubbleInt.const_mul ((C * Real.sqrt ell) ^ 2)
  have hSnonneg (r : ℝ) : 0 ≤ S r := by
    dsimp [S, affineJapaneseWeight]
    positivity
  have hPoint (r : ℝ) (hr : 0 < r) :
      S r ≤ (C * Real.sqrt ell) * bubble r := by
    have h :=
      actual_Hartree_full_mixed_Riesz_times_monopole_cubic_weighted_pointwise
        ell c r B A sigma hell hellOne hr hc hB hA
        hSigma z hz hSup hStrauss
    simpa only [S,C,D,F,V,Z,mul_assoc] using h
  have hSqPoint :
      ∀ᵐ r : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        S r ^ 2 ≤ (C * Real.sqrt ell) ^ 2 * bubble r ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hSq := pow_le_pow_left₀ (hSnonneg r) (hPoint r hr) 2
    simpa only [mul_pow] using hSq
  have hIntegral :
      (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
        ∫ r in Ioi (0 : ℝ),
          (C * Real.sqrt ell) ^ 2 * bubble r ^ 2 :=
    integral_mono_ae hSInt hMajorInt hSqPoint
  change (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
    C ^ 2 * ell * (∫ r in Ioi (0 : ℝ), bubble r ^ 2)
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ),
          (C * Real.sqrt ell) ^ 2 * bubble r ^ 2 := hIntegral
    _ = (C * Real.sqrt ell) ^ 2 *
        (∫ r in Ioi (0 : ℝ), bubble r ^ 2) := by rw [integral_const_mul]
    _ = _ := by rw [mul_pow, Real.sq_sqrt hell.le]

end HBL.TypeIIDynamicSelection
