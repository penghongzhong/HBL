import HBL.TypeIIDynamicSelection.ActualHartreeTrueQuadraticRieszCubicFiveWeight
import HBL.TypeIIDynamicSelection.ActualHartreeRieszMeasurability
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFullWeightedL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Native weighted L2 of a genuine Hartree quadratic Riesz-density Taylor atom

A fifth-power square majorant on the half-line produces the ORIGINAL
L^(2,7/4) space with the sharp integrable tail (1+r)^(-3/2).
The physical specialization uses a genuine complex two-scale background,
original radial inverse-square nonlocal kernel and actual quartic Taylor
density; it does NOT assign a false uniform bubble envelope to the radiation.

This controls one genuine quadratic nonlinear atom of the full PDE, not its
moving linear principal defect, remaining Taylor atoms, parameter Lipschitz,
finite higher-order recursion or final Type-II rate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Honest conversion from the polynomial fifth-weight square to the
native weighted L² class; the missing tail power is 3/2, not 1. -/
theorem actual_Hartree_fifth_weight_square_to_original_weighted_L2
    (F : ℝ → ℂ) (hF : Measurable F)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hFive : ∀ r : ℝ, 0 < r → (1 + r) ^ 5 * ‖F r‖ ^ 2 ≤ Q) :
    MemLp (fun r : ℝ =>
      affineJapaneseWeight (7 / 4 : ℝ) r * ‖F r‖)
      2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ),
      (affineJapaneseWeight (7 / 4 : ℝ) r * ‖F r‖) ^ 2) ≤
      Q * (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(3 / 2 : ℝ))) := by
  let S : ℝ → ℝ := fun r =>
    affineJapaneseWeight (7 / 4 : ℝ) r * ‖F r‖
  have hSm : Measurable S :=
    (affineJapaneseWeight_continuous (7 / 4 : ℝ)).measurable.mul hF.norm
  have hS0 (r : ℝ) : 0 ≤ S r := by
    dsimp [S, affineJapaneseWeight]
    positivity
  have hSq (r : ℝ) (hr : 0 < r) :
      S r ^ 2 ≤ Q * (1 + r) ^ (-(3 / 2 : ℝ)) := by
    have ht : 0 < 1 + r := by linarith
    have hBase : 1 + r ^ 2 ≤ (1 + r) ^ 2 := by
      nlinarith only [hr.le]
    have hLeft : (affineJapaneseWeight (7 / 4 : ℝ) r) ^ 2 =
        (1 + r ^ 2) ^ (7 / 4 : ℝ) := by
      unfold affineJapaneseWeight
      calc
        ((1 + r ^ 2) ^ ((7 / 4 : ℝ) / 2)) ^ 2 =
          ((1 + r ^ 2) ^ ((7 / 4 : ℝ) / 2)) ^ (2 : ℝ) :=
            (Real.rpow_natCast _ 2).symm
        _ = (1 + r ^ 2) ^ (((7 / 4 : ℝ) / 2) * 2) :=
          (Real.rpow_mul (by positivity) ((7 / 4 : ℝ) / 2) 2).symm
        _ = (1 + r ^ 2) ^ (7 / 4 : ℝ) := by norm_num
    have hRight : ((1 + r) ^ 2) ^ (7 / 4 : ℝ) =
        (1 + r) ^ (7 / 2 : ℝ) := by
      calc
        _ = ((1 + r) ^ (2 : ℝ)) ^ (7 / 4 : ℝ) := by
          rfl
        _ = (1 + r) ^ ((2 : ℝ) * (7 / 4 : ℝ)) :=
          (Real.rpow_mul ht.le 2 (7 / 4 : ℝ)).symm
        _ = _ := by norm_num
    have hWeight :
        (affineJapaneseWeight (7 / 4 : ℝ) r) ^ 2 ≤
          (1 + r) ^ (7 / 2 : ℝ) := by
      calc
        _ = (1 + r ^ 2) ^ (7 / 4 : ℝ) := hLeft
        _ ≤ ((1 + r) ^ 2) ^ (7 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hBase (by norm_num)
        _ = (1 + r) ^ (7 / 2 : ℝ) := hRight
    have hExp : (1 + r) ^ (7 / 2 : ℝ) =
        (1 + r) ^ (-(3 / 2 : ℝ)) * (1 + r) ^ 5 := by
      calc
        _ = (1 + r) ^ (-(3 / 2 : ℝ) + 5) := by norm_num
        _ = (1 + r) ^ (-(3 / 2 : ℝ)) *
              (1 + r) ^ (5 : ℝ) := Real.rpow_add ht _ _
        _ = (1 + r) ^ (-(3 / 2 : ℝ)) * (1 + r) ^ 5 := by
          rfl
    calc
      S r ^ 2 = (affineJapaneseWeight (7 / 4 : ℝ) r) ^ 2 *
          ‖F r‖ ^ 2 := by dsimp [S]; ring
      _ ≤ (1 + r) ^ (7 / 2 : ℝ) * ‖F r‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hWeight (sq_nonneg _)
      _ = (1 + r) ^ (-(3 / 2 : ℝ)) *
          ((1 + r) ^ 5 * ‖F r‖ ^ 2) := by rw [hExp]; ring
      _ ≤ (1 + r) ^ (-(3 / 2 : ℝ)) * Q :=
        mul_le_mul_of_nonneg_left (hFive r hr)
          (Real.rpow_nonneg ht.le _)
      _ = Q * (1 + r) ^ (-(3 / 2 : ℝ)) := by ring
  have hTailInt : IntegrableOn
      (fun r : ℝ => (1 + r) ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
    simpa only [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt
        (show -(3 / 2 : ℝ) < -1 by norm_num)
        (show -(1 : ℝ) < 0 by norm_num))
  have hMajorInt : IntegrableOn
      (fun r : ℝ => Q * (1 + r) ^ (-(3 / 2 : ℝ)))
      (Ioi (0 : ℝ)) := hTailInt.const_mul Q
  have hInt : IntegrableOn (fun r : ℝ => S r ^ 2) (Ioi (0 : ℝ)) := by
    apply hMajorInt.mono' (hSm.pow_const 2).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S r))]
    exact hSq r hr
  have hLp : MemLp S 2 halfLineMeasure :=
    (memLp_two_iff_integrable_sq hSm.aestronglyMeasurable.restrict).2 hInt
  change MemLp S 2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
      Q * (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(3 / 2 : ℝ)))
  refine ⟨hLp, ?_⟩
  calc
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
        ∫ r in Ioi (0 : ℝ), Q * (1 + r) ^ (-(3 / 2 : ℝ)) := by
      apply integral_mono_ae hInt hMajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hSq r hr
    _ = Q * (∫ r in Ioi (0 : ℝ),
          (1 + r) ^ (-(3 / 2 : ℝ))) := by rw [integral_const_mul]

/-- The preceding result is specialized to the original nonlocal quartic
Taylor atom on the actual two-scale Hartree background. -/
theorem actual_Hartree_true_two_scale_quadratic_Riesz_cubic_original_weighted_L2
    (ell c B A e : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (hA : 0 ≤ A) (he : 0 ≤ e)
    (z H : ℝ → ℂ)
    (hz : Measurable z) (hHmeas : Measurable H)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hStrauss : ∀ x : ℝ, 1 ≤ x → x * ‖z x‖ ≤ A)
    (hHB : ∀ x : ℝ, 0 < x → ‖H x‖ ≤ e * bubble x) :
    let U : ℝ → ℂ := fun x =>
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c x : ℂ) +
          rescalePhysicalRadiation ell z x
    let M : ℝ := 1 + monopoleRadialBoundConstant + B
    let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
    let E : ℝ := 2 * (B + A)
    let P : ℝ := ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) *
      actualHartreeBubbleSquaredRieszDecayConstant
    let K : ℝ := 2 * (D ^ 2 + E ^ 2)
    let F : ℝ → ℂ := fun r =>
      (radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r : ℂ) *
          actualHartreeComplexCubic (U r)
    MemLp (fun r : ℝ => affineJapaneseWeight (7 / 4 : ℝ) r * ‖F r‖)
      2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ),
      (affineJapaneseWeight (7 / 4 : ℝ) r * ‖F r‖) ^ 2) ≤
      (P ^ 2 * K ^ 3) *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(3 / 2 : ℝ))) := by
  dsimp only
  let U : ℝ → ℂ := fun x =>
    (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius c) c x : ℂ) +
        rescalePhysicalRadiation ell z x
  let M : ℝ := 1 + monopoleRadialBoundConstant + B
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let P : ℝ := ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) *
    actualHartreeBubbleSquaredRieszDecayConstant
  let K : ℝ := 2 * (D ^ 2 + E ^ 2)
  let F : ℝ → ℂ := fun r =>
    (radialHartreePotential
      (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r : ℂ) *
        actualHartreeComplexCubic (U r)
  have hVmeas := actual_Hartree_moving_monopole_measurable c
  have hUmeas : Measurable U := by
    dsimp [U, rescalePhysicalRadiation]
    fun_prop
  have hDensity : Measurable
      (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) := by
    unfold actualHartreeComplexDensityRemainder actualHartreeComplexRealPair
    fun_prop
  have hRiesz : Measurable
      (fun r => (radialHartreePotential
        (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r : ℂ)) :=
    Complex.measurable_ofReal.comp
      (actual_radialHartreePotential_measurable _ hDensity)
  have hCubic : Measurable (fun r => actualHartreeComplexCubic (U r)) := by
    unfold actualHartreeComplexCubic
    fun_prop
  have hFmeas : Measurable F := hRiesz.mul hCubic
  have hK : 0 ≤ K := by
    dsimp [K, D, E]
    positivity
  have hQ : 0 ≤ P ^ 2 * K ^ 3 :=
    mul_nonneg (sq_nonneg P) (pow_nonneg hK 3)
  have hFive (r : ℝ) (hr : 0 < r) :
      (1 + r) ^ 5 * ‖F r‖ ^ 2 ≤ P ^ 2 * K ^ 3 := by
    simpa only [F, P, K, D, E, M, U] using
      actual_Hartree_true_two_scale_quadratic_Riesz_cubic_fifth_weight
        ell c B A e hell hellOne hc hB hA he
        z H hz hHmeas hSup hStrauss hHB r hr
  exact actual_Hartree_fifth_weight_square_to_original_weighted_L2
    F hFmeas (P ^ 2 * K ^ 3) hQ hFive

end HBL.TypeIIDynamicSelection
