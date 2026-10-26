import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
Direct work on manuscript prop:regular-flow-stage3, not a new R environment.
This file proves concrete estimates for the actual three-dimensional kernel
and the actual seventh-order complex Hartree nonlinearity. It does NOT assert
the Sobolev local flow, parameter regularity, or time jets.
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

/-- Absolute convergence and a uniform bound for the actual convolution. -/
theorem potential_bound (ρ : Space → ℂ) (hρ : Integrable ρ)
    (M : ℝ) (_hM : 0 ≤ M) (hb : ∀ᵐ y, ‖ρ y‖ ≤ M) (x : Space) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) * ρ y) ∧
      ‖potential ρ x‖ ≤ nearMass * M + ∫ y : Space, ‖ρ y‖ := by
  have hm : Integrable (fun y : Space => nearKernel (x - y) * M + ‖ρ y‖) :=
    ((near_integrable.comp_sub_left x).mul_const M).add hρ.norm
  have hk : Measurable (fun y : Space => (kernel (x - y) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
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

/-- Signed/complex differences, not merely positive densities. -/
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

/-- Quartic density difference controlled by the physical complex increment. -/
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

/-- The actual quartic density, as a complex-valued function. -/
def quarticDensity (f : Space → ℂ) (x : Space) : ℂ := (‖f x‖ ^ 4 : ℝ)

/-- The original Hartree nonlinearity, with its physical coefficient. -/
def hartreeNonlinearity (κ : ℝ) (f : Space → ℂ) (x : Space) : ℂ :=
  (κ : ℂ) * potential (quarticDensity f) x * ((‖f x‖ ^ 2 : ℂ) * f x)

private theorem quartic_integrable (f : Space → ℂ) (hf : MemLp f 2)
    (R : ℝ) (hb : ∀ᵐ x, ‖f x‖ ≤ R) :
    Integrable (fun x : Space => ‖f x‖ ^ 4) ∧
    (∫ x : Space, ‖f x‖ ^ 4) ≤ R ^ 2 * (∫ x : Space, ‖f x‖ ^ 2) := by
  have h2 := hf.norm.integrable_sq
  have hl : ∀ᵐ x, ‖‖f x‖ ^ 4‖ ≤ R ^ 2 * ‖f x‖ ^ 2 := by
    filter_upwards [hb] with x hx
    have hs := pow_le_pow_left₀ (norm_nonneg (f x)) hx 2
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖f x‖)]
  have hi : Integrable (fun x : Space => ‖f x‖ ^ 4) :=
    (h2.const_mul (R ^ 2)).mono' (hf.aestronglyMeasurable.norm.pow 4) hl
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi (h2.const_mul (R ^ 2))
    (hl.mono fun x hx => by simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using hx)
  rwa [integral_const_mul] at h

/-- Actual quartic potential: density integrability is derived, not assumed. -/
theorem quartic_potential_bound (f : Space → ℂ) (hf : MemLp f 2)
    (R : ℝ) (hb : ∀ᵐ x, ‖f x‖ ≤ R) (x : Space) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) * quarticDensity f y) ∧
    ‖potential (quarticDensity f) x‖ ≤
      nearMass * R ^ 4 + R ^ 2 * (∫ y : Space, ‖f y‖ ^ 2) := by
  have hd := quartic_integrable f hf R hb
  have hρ : Integrable (quarticDensity f) := hd.1.ofReal
  have hbρ : ∀ᵐ y, ‖quarticDensity f y‖ ≤ R ^ 4 := by
    filter_upwards [hb] with y hy
    simpa only [quarticDensity, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using
      pow_le_pow_left₀ (norm_nonneg (f y)) hy 4
  have h := potential_bound (quarticDensity f) hρ (R ^ 4) (by positivity) hbρ x
  have he : (∫ y : Space, ‖quarticDensity f y‖) = ∫ y : Space, ‖f y‖ ^ 4 := by
    apply integral_congr_ae
    filter_upwards with y
    simp only [quarticDensity, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
  rw [he] at h
  exact ⟨h.1, h.2.trans (add_le_add_left hd.2 _)⟩

private theorem potential_measurable (ρ : Space → ℂ) (hρ : AEStronglyMeasurable ρ) :
    AEStronglyMeasurable (potential ρ) := by
  have hk : Measurable (fun p : Space × Space => (kernel (p.1 - p.2) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (kernel_measurable.comp (measurable_fst.sub measurable_snd))
  have hm : AEStronglyMeasurable
      (fun p : Space × Space => (kernel (p.1 - p.2) : ℂ) * ρ p.2)
      ((volume : Measure Space).prod volume) :=
    hk.aestronglyMeasurable.mul hρ.comp_snd
  exact hm.integral_prod_right'

/-- Genuine seventh-order Hartree L2 estimate. This is the order-zero
estimate, not the H^L local-flow theorem. -/
theorem hartree_L2_bound (κ : ℝ) (f : Space → ℂ) (hf : MemLp f 2)
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ᵐ x, ‖f x‖ ≤ R)
    (hE : (∫ x : Space, ‖f x‖ ^ 2) ≤ R ^ 2) :
    MemLp (hartreeNonlinearity κ f) 2 ∧
    (∫ x : Space, ‖hartreeNonlinearity κ f x‖ ^ 2) ≤
      (|κ| * (nearMass + 1) * R ^ 6) ^ 2 * (∫ x : Space, ‖f x‖ ^ 2) := by
  have hn : 0 ≤ nearMass := integral_nonneg near_nonneg
  have hB : 0 ≤ (nearMass + 1) * R ^ 4 := by positivity
  have hP (x : Space) : ‖potential (quarticDensity f) x‖ ≤ (nearMass + 1) * R ^ 4 := by
    have h := (quartic_potential_bound f hf R hb x).2
    have he := mul_le_mul_of_nonneg_left hE (sq_nonneg R)
    nlinarith only [h, he]
  have hρ : AEStronglyMeasurable (quarticDensity f) :=
    (quartic_integrable f hf R hb).1.ofReal.aestronglyMeasurable
  have hc : AEStronglyMeasurable (fun x : Space => ((‖f x‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (hf.aestronglyMeasurable.norm.pow 2)
  have hm : AEStronglyMeasurable (hartreeNonlinearity κ f) :=
    ((potential_measurable _ hρ).const_mul (κ : ℂ)).mul (hc.mul hf.aestronglyMeasurable)
  have hl : ∀ᵐ x, ‖hartreeNonlinearity κ f x‖ ≤
      (|κ| * (nearMass + 1) * R ^ 6) * ‖f x‖ := by
    filter_upwards [hb] with x hx
    have hs := pow_le_pow_left₀ (norm_nonneg (f x)) hx 2
    have hA := mul_le_mul_of_nonneg_left (hP x) (abs_nonneg κ)
    have hC := mul_le_mul_of_nonneg_right hs (norm_nonneg (f x))
    have hp := mul_le_mul hA hC
      (show 0 ≤ ‖f x‖ ^ 2 * ‖f x‖ by positivity)
      (mul_nonneg (abs_nonneg κ) hB)
    calc
      ‖hartreeNonlinearity κ f x‖ =
          |κ| * ‖potential (quarticDensity f) x‖ * (‖f x‖ ^ 2 * ‖f x‖) := by
        simp only [hartreeNonlinearity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg ‖f x‖)]
      _ ≤ (|κ| * ((nearMass + 1) * R ^ 4)) * (R ^ 2 * ‖f x‖) := hp
      _ = _ := by ring
  have hi : MemLp (hartreeNonlinearity κ f) 2 := hf.of_le_mul hm hl
  refine ⟨hi, ?_⟩
  have hb2 : ∀ᵐ x, ‖hartreeNonlinearity κ f x‖ ^ 2 ≤
      (|κ| * (nearMass + 1) * R ^ 6) ^ 2 * ‖f x‖ ^ 2 := by
    filter_upwards [hl] with x hx
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 2
  have he := integral_mono_ae hi.norm.integrable_sq
    (hf.norm.integrable_sq.const_mul ((|κ| * (nearMass + 1) * R ^ 6) ^ 2)) hb2
  rwa [integral_const_mul] at he

/-- Kernel checks only: the original manuscript environment is still pending. -/
theorem regularRadiationKernel_checks :
    Integrable nearKernel ∧ 0 ≤ nearMass ∧
    (∀ ρ : Space → ℂ, Integrable ρ → ∀ M : ℝ, 0 ≤ M →
      (∀ᵐ y, ‖ρ y‖ ≤ M) → ∀ x : Space,
        Integrable (fun y : Space => (kernel (x - y) : ℂ) * ρ y) ∧
        ‖potential ρ x‖ ≤ nearMass * M + ∫ y : Space, ‖ρ y‖) :=
  ⟨near_integrable, integral_nonneg near_nonneg, potential_bound⟩

end HBL.RegularRadiation
