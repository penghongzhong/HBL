import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
Direct work on manuscript prop:regular-flow-stage3, not a new R environment.
This file proves a concrete estimate for the actual three-dimensional kernel.
It does NOT assert the Sobolev local flow, parameter regularity, or time jets.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal ENNReal
namespace HBL.RegularRadiation

abbrev Space := EuclideanSpace ℝ (Fin 3)

def kernel (x : Space) : ℝ := (‖x‖ ^ 2)⁻¹
def nearKernel (x : Space) : ℝ := (ball (0 : Space) 1).indicator kernel x
def nearMass : ℝ := ∫ x : Space, nearKernel x

def potential (ρ : Space → ℂ) (x : Space) : ℂ :=
  ∫ y : Space, (kernel (x - y) : ℂ) * ρ y

private theorem kernel_measurable : Measurable kernel := by
  unfold kernel
  fun_prop

private theorem near_nonneg (x : Space) : 0 ≤ nearKernel x := by
  exact indicator_nonneg (fun _ _ => inv_nonneg.mpr (sq_nonneg _)) _

private theorem near_integrable : Integrable nearKernel := by
  apply (integrable_indicator_iff measurableSet_ball).mpr
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2)
    (by norm_num [Space]) (by norm_num [Space])
  · filter_upwards with x
    simp only [kernel, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (‖x‖ ^ 2)⁻¹), one_mul]
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
  · exact kernel_measurable.aestronglyMeasurable

private theorem kernel_split_bound (x : Space) : kernel x ≤ nearKernel x + 1 := by
  by_cases hx : x ∈ ball (0 : Space) 1
  · simp only [nearKernel, indicator_of_mem hx]
    linarith
  · have hn : 1 ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    have hs : 1 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hi : (‖x‖ ^ 2)⁻¹ ≤ (1 : ℝ) := by
      simpa only [one_div, inv_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs)
    simpa only [nearKernel, indicator_of_notMem hx, zero_add, kernel] using hi

/-- Absolute convergence and a uniform bound for the actual convolution,
for every physical point. Only natural input density conditions are assumed. -/
theorem potential_bound (ρ : Space → ℂ) (hρ : Integrable ρ)
    (M : ℝ) (_hM : 0 ≤ M) (hb : ∀ᵐ y, ‖ρ y‖ ≤ M) (x : Space) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) * ρ y) ∧
      ‖potential ρ x‖ ≤ nearMass * M + ∫ y : Space, ‖ρ y‖ := by
  have hm : Integrable (fun y : Space => nearKernel (x - y) * M + ‖ρ y‖) :=
    ((near_integrable.comp_sub_left x).mul_const M).add hρ.norm
  have hk : Measurable (fun y : Space => (kernel (x - y) : ℂ)) := by
    exact Complex.continuous_ofReal.measurable.comp
      (kernel_measurable.comp (measurable_const.sub measurable_id))
  have hle : ∀ᵐ y, ‖(kernel (x - y) : ℂ) * ρ y‖ ≤
      nearKernel (x - y) * M + ‖ρ y‖ := by
    filter_upwards [hb] with y hy
    have h0 : 0 ≤ kernel (x - y) := inv_nonneg.mpr (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right (kernel_split_bound (x - y)) (norm_nonneg (ρ y))
    have h2 := mul_le_mul_of_nonneg_left hy (near_nonneg (x - y))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    nlinarith only [h1, h2]
  have hi : Integrable (fun y : Space => (kernel (x - y) : ℂ) * ρ y) :=
    hm.mono' (hk.aestronglyMeasurable.mul hρ.aestronglyMeasurable) hle
  refine ⟨hi, ?_⟩
  have h := (norm_integral_le_integral_norm (fun y : Space =>
    (kernel (x - y) : ℂ) * ρ y)).trans (integral_mono_ae hi.norm hm hle)
  rw [integral_add ((near_integrable.comp_sub_left x).mul_const M) hρ.norm,
    integral_mul_const, integral_sub_left_eq_self] at h
  exact h

/-- A real density can change sign; this is the difference estimate needed
when comparing radiation data, not merely a positivity estimate. -/
theorem potential_sub_bound (ρ σ : Space → ℂ)
    (hρ : Integrable ρ) (hσ : Integrable σ)
    (Mρ Mσ D : ℝ) (hMρ : 0 ≤ Mρ) (hMσ : 0 ≤ Mσ) (hD : 0 ≤ D)
    (hρb : ∀ᵐ y, ‖ρ y‖ ≤ Mρ) (hσb : ∀ᵐ y, ‖σ y‖ ≤ Mσ)
    (hdb : ∀ᵐ y, ‖ρ y - σ y‖ ≤ D) (x : Space) :
    ‖potential ρ x - potential σ x‖ ≤
      nearMass * D + ∫ y : Space, ‖ρ y - σ y‖ := by
  have h := potential_bound (fun y => ρ y - σ y) (hρ.sub hσ) D hD hdb x
  have he : potential (fun y => ρ y - σ y) x = potential ρ x - potential σ x := by
    unfold potential
    simp_rw [mul_sub]
    exact integral_sub (potential_bound ρ hρ Mρ hMρ hρb x).1
      (potential_bound σ hσ Mσ hMσ hσb x).1
  rw [he] at h
  exact h.2

/-- The quartic density difference is controlled by the physical complex
increment. This estimate is used before integrating the singular kernel. -/
theorem quartic_difference (z w : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    |‖z‖ ^ 4 - ‖w‖ ^ 4| ≤
      (2 * R ^ 2) * (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have ha : |‖z‖ ^ 4 - ‖w‖ ^ 4| =
      |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    rw [show ‖z‖ ^ 4 - ‖w‖ ^ 4 =
      (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) * (‖z‖ ^ 2 + ‖w‖ ^ 2) by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ ‖z‖ + ‖w‖ by positivity),
      abs_of_nonneg (show 0 ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 by positivity)]
  have hsq : ‖z‖ ^ 2 + ‖w‖ ^ 2 ≤ 2 * R ^ 2 := by
    nlinarith [sq_nonneg (R - ‖z‖), sq_nonneg (R - ‖w‖),
      mul_nonneg (sub_nonneg.mpr hz) (add_nonneg hR (norm_nonneg z)),
      mul_nonneg (sub_nonneg.mpr hw) (add_nonneg hR (norm_nonneg w))]
  rw [ha]
  have hfirst := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w)
    (show 0 ≤ ‖z‖ + ‖w‖ by positivity)
  have hprod := mul_le_mul hfirst hsq
    (show 0 ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 by positivity)
    (show 0 ≤ ‖z - w‖ * (‖z‖ + ‖w‖) by positivity)
  calc
    _ ≤ ‖z - w‖ * (‖z‖ + ‖w‖) * (2 * R ^ 2) := hprod
    _ = _ := by ring

/-- This audit entry covers kernel estimates only. The original manuscript
lemma remains pending until the actual Sobolev flow and all time jets compile. -/
theorem regularRadiationKernel_checks :
    Integrable nearKernel ∧ 0 ≤ nearMass ∧
    (∀ ρ : Space → ℂ, Integrable ρ → ∀ M : ℝ, 0 ≤ M →
      (∀ᵐ y, ‖ρ y‖ ≤ M) → ∀ x : Space,
        Integrable (fun y : Space => (kernel (x - y) : ℂ) * ρ y) ∧
        ‖potential ρ x‖ ≤ nearMass * M + ∫ y : Space, ‖ρ y‖) :=
  ⟨near_integrable, integral_nonneg near_nonneg, potential_bound⟩

end HBL.RegularRadiation
