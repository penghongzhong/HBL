import HBL.InnerReconstruction.RepresentativeFirstMomentTrace
import HBL.ActualInnerAffinelyCorrected
import Mathlib.Tactic

/-!
Uniform first-moment estimates for the ACTUAL two fixed Hartree Fredholm
operators. The inverse constants are derived from their proved compactness,
not supplied as hypotheses. Every source norm is the original weighted
half-line L2 realization. This file is an operator estimate, not nonlinear
three-region closure or a Type-II rate theorem.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

private theorem actual_l2_integral_norm_product_le
    (f g : RealL2 halfLineMeasure) :
    (∫ r, ‖f r * g r‖ ∂halfLineMeasure) ≤ ‖f‖ * ‖g‖ := by
  let fn : RealL2 halfLineMeasure :=
    ((Lp.memLp f).norm).toLp (fun r => ‖f r‖)
  let gn : RealL2 halfLineMeasure :=
    ((Lp.memLp g).norm).toLp (fun r => ‖g r‖)
  have hfn : ‖fn‖ = ‖f‖ := by
    calc
      ‖fn‖ = (eLpNorm (fn : ℝ → ℝ) 2 halfLineMeasure).toReal := rfl
      _ = (eLpNorm (fun r => ‖f r‖) 2 halfLineMeasure).toReal :=
        congrArg ENNReal.toReal (eLpNorm_congr_ae ((Lp.memLp f).norm).coeFn_toLp)
      _ = ‖f‖ := congrArg ENNReal.toReal
        (eLpNorm_norm (f : ℝ → ℝ) (Lp.aestronglyMeasurable f))
  have hgn : ‖gn‖ = ‖g‖ := by
    calc
      ‖gn‖ = (eLpNorm (gn : ℝ → ℝ) 2 halfLineMeasure).toReal := rfl
      _ = (eLpNorm (fun r => ‖g r‖) 2 halfLineMeasure).toReal :=
        congrArg ENNReal.toReal (eLpNorm_congr_ae ((Lp.memLp g).norm).coeFn_toLp)
      _ = ‖g‖ := congrArg ENNReal.toReal
        (eLpNorm_norm (g : ℝ → ℝ) (Lp.aestronglyMeasurable g))
  have heq : (∫ r, ‖f r * g r‖ ∂halfLineMeasure) =
      inner ℝ fn gn := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((Lp.memLp f).norm).coeFn_toLp,
      ((Lp.memLp g).norm).coeFn_toLp] with r hf hg
    change ‖f r * g r‖ = inner ℝ (fn r) (gn r)
    rw [hf, hg, Real.inner_apply, norm_mul]
  rw [heq]
  calc
    inner ℝ fn gn ≤ ‖fn‖ * ‖gn‖ := real_inner_le_norm _ _
    _ = ‖f‖ * ‖g‖ := by rw [hfn, hgn]

def actualInnerPotentialMomentWeightL2 : RealL2 halfLineMeasure :=
  weightedGreenOutputMajorant_memLp_two.toLp weightedGreenOutputMajorant

def actualInnerSourceMomentWeightL2 : RealL2 halfLineMeasure :=
  (weightedSource_momentWeight_memLp (7 / 4 : ℝ) (by norm_num)).toLp
    (fun r => r * affineJapaneseDecay (7 / 4 : ℝ) r)

/-- The existing concrete Green first-moment bound has a fixed L2 operator
bound. Both terms, including the potential times the Hilbert unknown, remain. -/
theorem actual_innerGreenBound_le_fixed_weight_norms
    (g : RealL2 halfLineMeasure) (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) :
    innerGreenBound g F ≤
      ‖actualInnerPotentialMomentWeightL2‖ * ‖g‖ +
      ‖actualInnerSourceMomentWeightL2‖ *
        ‖weightedSourceDataL2 (7 / 4 : ℝ) F hF‖ := by
  have hPot : weightedGreenPrimitiveBound g ≤
      ‖actualInnerPotentialMomentWeightL2‖ * ‖g‖ := by
    have heq : weightedGreenPrimitiveBound g =
        ∫ r, ‖actualInnerPotentialMomentWeightL2 r * g r‖ ∂halfLineMeasure := by
      unfold weightedGreenPrimitiveBound
      apply integral_congr_ae
      filter_upwards [weightedGreenOutputMajorant_memLp_two.coeFn_toLp] with r hr
      change actualInnerPotentialMomentWeightL2 r = weightedGreenOutputMajorant r at hr
      rw [hr]
    rw [heq]
    exact actual_l2_integral_norm_product_le _ _
  have hSrc : (∫ r, ‖r * F r‖ ∂halfLineMeasure) ≤
      ‖actualInnerSourceMomentWeightL2‖ *
        ‖weightedSourceDataL2 (7 / 4 : ℝ) F hF‖ := by
    have heq : (∫ r, ‖r * F r‖ ∂halfLineMeasure) =
        ∫ r, ‖actualInnerSourceMomentWeightL2 r *
          weightedSourceDataL2 (7 / 4 : ℝ) F hF r‖ ∂halfLineMeasure := by
      apply integral_congr_ae
      filter_upwards [
        (weightedSource_momentWeight_memLp (7 / 4 : ℝ) (by norm_num)).coeFn_toLp,
        weightedSourceDataL2_ae (7 / 4 : ℝ) F hF] with r hw hd
      change actualInnerSourceMomentWeightL2 r =
        r * affineJapaneseDecay (7 / 4 : ℝ) r at hw
      rw [hw, hd]
      congr 1
      calc
        r * F r = r * (affineJapaneseDecay (7 / 4 : ℝ) r *
            affineJapaneseWeight (7 / 4 : ℝ) r) * F r := by
          rw [affineJapaneseDecay_mul_weight, mul_one]
        _ = _ := by ring
    rw [heq]
    exact actual_l2_integral_norm_product_le _ _
  exact _root_.add_le_add hPot hSrc

/-- Fixed, derived constants bound both actual normalized inner moments
by the corresponding corrected-source weighted L2 norms. Neither the
scale nor the moving core occurs in the chosen constants. -/
theorem actual_inner_fixed_Fredholm_moment_constants :
    ∃ Dp Dm : ℝ, 0 ≤ Dp ∧ 0 ≤ Dm ∧
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
        (x : InnerCorrections),
      (1 - weightedBirmanSchwingerOperator) (x.1 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
          (weightedSourceDataL2 (7 / 4 : ℝ) Fp hp) →
      (1 - weightedPhaseBirman) (x.2 : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
          (weightedSourceDataL2 (7 / 4 : ℝ) Fm hm) →
      innerGreenBound (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure)) Fp ≤
        Dp * ‖weightedSourceDataL2 (7 / 4 : ℝ) Fp hp‖ ∧
      innerGreenBound ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure)) Fm ≤
        Dm * ‖weightedSourceDataL2 (7 / 4 : ℝ) Fm hm‖ := by
  obtain ⟨Cp, hCp⟩ := HBL.Fredholm.one_sub_antilipschitz_on_kernelComplement
    weightedBirmanSchwingerOperator_compact
  obtain ⟨Cm, hCm⟩ := HBL.Fredholm.one_sub_antilipschitz_on_kernelComplement
    weightedPhaseBirman_compact
  let S := weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
  let Na : ℝ := ‖actualInnerPotentialMomentWeightL2‖
  let Ns : ℝ := ‖actualInnerSourceMomentWeightL2‖
  let Dp : ℝ := Na * ‖weightedPotentialOperator‖ * ((Cp : ℝ) * ‖S‖) + Ns
  let Dm : ℝ := Na * 3 * ((Cm : ℝ) * ‖S‖) + Ns
  refine ⟨Dp, Dm, by dsimp [Dp, Na, Ns]; positivity,
    by dsimp [Dm, Na, Ns]; positivity, ?_⟩
  intro Fp Fm hp hm x hxp hxm
  let dp := weightedSourceDataL2 (7 / 4 : ℝ) Fp hp
  let dm := weightedSourceDataL2 (7 / 4 : ℝ) Fm hm
  have hxp0 : ‖(x.1 : RealL2 halfLineMeasure)‖ ≤
      (Cp : ℝ) * ‖(1 - weightedBirmanSchwingerOperator)
        (x.1 : RealL2 halfLineMeasure)‖ := by
    have h := hCp.le_mul_dist x.1 0
    change dist (x.1 : RealL2 halfLineMeasure) 0 ≤
      (Cp : ℝ) * dist ((1 - weightedBirmanSchwingerOperator)
        (x.1 : RealL2 halfLineMeasure)) ((1 - weightedBirmanSchwingerOperator) 0) at h
    simpa only [map_zero, dist_zero_right] using h
  have hxm0 : ‖(x.2 : RealL2 halfLineMeasure)‖ ≤
      (Cm : ℝ) * ‖(1 - weightedPhaseBirman)
        (x.2 : RealL2 halfLineMeasure)‖ := by
    have h := hCm.le_mul_dist x.2 0
    change dist (x.2 : RealL2 halfLineMeasure) 0 ≤
      (Cm : ℝ) * dist ((1 - weightedPhaseBirman)
        (x.2 : RealL2 halfLineMeasure)) ((1 - weightedPhaseBirman) 0) at h
    simpa only [map_zero, dist_zero_right] using h
  have hxp1 : ‖(x.1 : RealL2 halfLineMeasure)‖ ≤
      ((Cp : ℝ) * ‖S‖) * ‖dp‖ := by
    rw [hxp] at hxp0
    exact hxp0.trans ((mul_le_mul_of_nonneg_left (S.le_opNorm dp) Cp.coe_nonneg).trans_eq
      (by ring))
  have hxm1 : ‖(x.2 : RealL2 halfLineMeasure)‖ ≤
      ((Cm : ℝ) * ‖S‖) * ‖dm‖ := by
    rw [hxm] at hxm0
    exact hxm0.trans ((mul_le_mul_of_nonneg_left (S.le_opNorm dm) Cm.coe_nonneg).trans_eq
      (by ring))
  constructor
  · have hV := (weightedPotentialOperator.le_opNorm
        (x.1 : RealL2 halfLineMeasure)).trans
      (mul_le_mul_of_nonneg_left hxp1 (norm_nonneg _))
    calc
      _ ≤ Na * ‖weightedPotentialOperator (x.1 : RealL2 halfLineMeasure)‖ +
          Ns * ‖dp‖ := actual_innerGreenBound_le_fixed_weight_norms _ Fp hp
      _ ≤ Na * (‖weightedPotentialOperator‖ *
          (((Cp : ℝ) * ‖S‖) * ‖dp‖)) + Ns * ‖dp‖ :=
        _root_.add_le_add (mul_le_mul_of_nonneg_left hV
          (show 0 ≤ Na from norm_nonneg _)) (le_refl _)
      _ = Dp * ‖dp‖ := by dsimp [Dp]; ring
  · have hV : ‖(3 : ℝ) • (x.2 : RealL2 halfLineMeasure)‖ ≤
        3 * (((Cm : ℝ) * ‖S‖) * ‖dm‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact mul_le_mul_of_nonneg_left hxm1 (by norm_num)
    calc
      _ ≤ Na * ‖(3 : ℝ) • (x.2 : RealL2 halfLineMeasure)‖ + Ns * ‖dm‖ :=
        actual_innerGreenBound_le_fixed_weight_norms _ Fm hm
      _ ≤ Na * (3 * (((Cm : ℝ) * ‖S‖) * ‖dm‖)) + Ns * ‖dm‖ :=
        _root_.add_le_add (mul_le_mul_of_nonneg_left hV
          (show 0 ≤ Na from norm_nonneg _)) (le_refl _)
      _ = Dm * ‖dm‖ := by dsimp [Dm]; ring

end HBL.Modulation.Monopole
