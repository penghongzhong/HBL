import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The nonzero cosine coefficients of `log (sin x)` on `(0, π)`.

This is the scalar analytic input for the angular logarithmic Hartree
kernel.  The endpoint singularities are kept explicit; no Fourier-series
identity is assumed.
-/

noncomputable section

open Set MeasureTheory
open Filter
open scoped Interval Topology

namespace HBL

theorem tendsto_truncated_intervalIntegral
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 Real.pi) :
    Tendsto (fun epsilon : ℝ =>
        ∫ x : ℝ in epsilon..Real.pi - epsilon, f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : ℝ in 0..Real.pi, f x)) := by
  have hhalf : 0 < Real.pi / 2 := by positivity
  have hevent : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      0 < epsilon ∧ epsilon < Real.pi / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hhalf)] with epsilon hpos hlt
    exact ⟨hpos, hlt⟩
  let F : ℝ → ℝ := fun b => ∫ x : ℝ in 0..b, f x
  have hzero_mem : (0 : ℝ) ∈ [[(0 : ℝ), Real.pi]] := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact left_mem_Icc.mpr Real.pi_pos.le
  have hpi_mem : Real.pi ∈ [[(0 : ℝ), Real.pi]] := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact right_mem_Icc.mpr Real.pi_pos.le
  have hF : ContinuousOn F [[(0 : ℝ), Real.pi]] :=
    intervalIntegral.continuousOn_primitive_interval' hf hzero_mem
  have hid0 : Tendsto (fun epsilon : ℝ => epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left inf_le_left
  have hepsilon_mem : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      epsilon ∈ [[(0 : ℝ), Real.pi]] := by
    filter_upwards [hevent] with epsilon hepsilon
    rw [uIcc_of_le Real.pi_pos.le]
    constructor
    · exact hepsilon.1.le
    · linarith [Real.pi_pos]
  have hepsilon_within : Tendsto (fun epsilon : ℝ => epsilon)
      (𝓝[>] (0 : ℝ))
      (nhdsWithin (0 : ℝ) [[(0 : ℝ), Real.pi]]) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ hid0 hepsilon_mem
  have hFepsilon : Tendsto (fun epsilon : ℝ => F epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
    simpa only [Function.comp_def] using
      (hF 0 hzero_mem).tendsto.comp hepsilon_within
  have hright0 : Tendsto (fun epsilon : ℝ => Real.pi - epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := by
    convert tendsto_const_nhds.sub hid0 using 1 <;> ring
  have hright_mem : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      Real.pi - epsilon ∈ [[(0 : ℝ), Real.pi]] := by
    filter_upwards [hevent] with epsilon hepsilon
    rw [uIcc_of_le Real.pi_pos.le]
    constructor <;> linarith [Real.pi_pos]
  have hright_within : Tendsto (fun epsilon : ℝ => Real.pi - epsilon)
      (𝓝[>] (0 : ℝ))
      (nhdsWithin Real.pi [[(0 : ℝ), Real.pi]]) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ hright0 hright_mem
  have hFright : Tendsto (fun epsilon : ℝ => F (Real.pi - epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 (F Real.pi)) := by
    simpa only [Function.comp_def] using
      (hF Real.pi hpi_mem).tendsto.comp hright_within
  have hdiff := hFright.sub hFepsilon
  have heq : (fun epsilon : ℝ =>
      F (Real.pi - epsilon) - F epsilon) =ᶠ[𝓝[>] (0 : ℝ)]
      fun epsilon : ℝ =>
        ∫ x : ℝ in epsilon..Real.pi - epsilon, f x := by
    filter_upwards [hevent] with epsilon hepsilon
    have he_mem : epsilon ∈ [[(0 : ℝ), Real.pi]] := by
      rw [uIcc_of_le Real.pi_pos.le]
      constructor
      · exact hepsilon.1.le
      · linarith [Real.pi_pos]
    have hr_mem : Real.pi - epsilon ∈ [[(0 : ℝ), Real.pi]] := by
      rw [uIcc_of_le Real.pi_pos.le]
      constructor <;> linarith [Real.pi_pos]
    apply intervalIntegral.integral_interval_sub_left
    · apply hf.mono_set
      exact uIcc_subset_uIcc hzero_mem hr_mem
    · apply hf.mono_set
      exact uIcc_subset_uIcc hzero_mem he_mem
  have hlimit : F Real.pi - F 0 = ∫ x : ℝ in 0..Real.pi, f x := by
    simp [F]
  rw [hlimit] at hdiff
  exact hdiff.congr' heq

/-- A continuous representative of `sin (2 n x) cot x`. -/
def cotSinePolynomial (n : ℕ) (x : ℝ) : ℝ :=
  2 * Real.cos x *
    ∑ i ∈ Finset.range n, Real.cos (2 * x * i + x)

theorem cotSinePolynomial_continuous (n : ℕ) :
    Continuous (cotSinePolynomial n) := by
  unfold cotSinePolynomial
  fun_prop

theorem sin_mul_cotSinePolynomial (n : ℕ) (x : ℝ) :
    Real.sin x * cotSinePolynomial n x =
      Real.sin (2 * n * x) * Real.cos x := by
  have h := Real.sin_mul_sum_cos n (2 * x) x
  unfold cotSinePolynomial
  have h' :
      Real.sin x *
          (∑ i ∈ Finset.range n, Real.cos (2 * x * i + x)) =
        Real.sin ((n : ℝ) * x) * Real.cos ((n : ℝ) * x) := by
    convert h using 1 <;> push_cast <;> ring
  rw [show 2 * (n : ℝ) * x = 2 * ((n : ℝ) * x) by ring,
    Real.sin_two_mul]
  linear_combination 2 * Real.cos x * h'

theorem cotSinePolynomial_eq (n : ℕ) (x : ℝ)
    (hx : Real.sin x ≠ 0) :
    cotSinePolynomial n x =
      Real.sin (2 * n * x) * Real.cos x / Real.sin x := by
  apply (mul_left_cancel₀ hx)
  rw [mul_div_cancel₀ _ hx]
  exact sin_mul_cotSinePolynomial n x

theorem intervalIntegrable_log_sin_mul_cos (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ => Real.log (Real.sin x) * Real.cos (2 * n * x))
      volume 0 Real.pi := by
  exact intervalIntegrable_log_sin.mul_continuousOn
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_const |>.mul continuous_id)).continuousOn)

theorem integral_cos_two_nat_mul (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in 0..Real.pi, Real.cos (2 * n * x)) = 0 := by
  have hc : (2 * (n : ℝ)) ≠ 0 := by positivity
  rw [show (fun x : ℝ => Real.cos (2 * n * x)) =
      fun x : ℝ => Real.cos ((2 * (n : ℝ)) * x) by
        funext x
        push_cast
        rfl]
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, mul_eq_zero,
    inv_eq_zero]
  right
  convert Real.sin_nat_mul_pi (2 * n) using 1 <;> push_cast <;> ring

theorem cotSinePolynomial_succ (n : ℕ) (x : ℝ) :
    cotSinePolynomial n.succ x =
      cotSinePolynomial n x +
        Real.cos (2 * (n + 1) * x) + Real.cos (2 * n * x) := by
  calc
    cotSinePolynomial n.succ x =
        cotSinePolynomial n x +
          2 * Real.cos x * Real.cos (2 * x * n + x) := by
      unfold cotSinePolynomial
      rw [Finset.sum_range_succ]
      ring
    _ = cotSinePolynomial n x +
          (Real.cos (x - (2 * x * n + x)) +
            Real.cos (x + (2 * x * n + x))) := by
      rw [Real.two_mul_cos_mul_cos]
    _ = cotSinePolynomial n x +
          Real.cos (2 * (n + 1) * x) + Real.cos (2 * n * x) := by
      rw [show x - (2 * x * (n : ℝ) + x) = -(2 * n * x) by ring,
        Real.cos_neg]
      rw [show x + (2 * x * (n : ℝ) + x) =
        2 * ((n : ℝ) + 1) * x by ring]
      ring

theorem cotSinePolynomial_succ_fun (n : ℕ) :
    cotSinePolynomial n.succ = fun x : ℝ =>
      cotSinePolynomial n x +
        Real.cos (2 * (n + 1) * x) + Real.cos (2 * n * x) := by
  funext x
  exact cotSinePolynomial_succ n x

theorem cotSinePolynomial_intervalIntegral (n : ℕ) :
    (∫ x : ℝ in 0..Real.pi, cotSinePolynomial n.succ x) =
      Real.pi := by
  induction n with
  | zero =>
      rw [cotSinePolynomial_succ_fun 0]
      simp only [cotSinePolynomial, Finset.range_zero, Finset.sum_empty,
        mul_zero, zero_add, Nat.cast_one, Nat.cast_zero]
      rw [intervalIntegral.integral_add
        (by exact (by fun_prop : Continuous
          (fun x : ℝ => Real.cos (2 * 1 * x))).intervalIntegrable _ _)
        (by exact (by fun_prop : Continuous
          (fun x : ℝ => Real.cos (0 * x))).intervalIntegrable _ _)]
      simp only [Nat.cast_one, mul_one, Nat.cast_zero]
      have hcos :
          (∫ x : ℝ in 0..Real.pi, Real.cos (2 * x)) = 0 := by
        simpa only [Nat.cast_one, mul_one] using
          integral_cos_two_nat_mul 1 (by omega)
      rw [hcos]
      simp
  | succ n ih =>
      change (∫ x : ℝ in 0..Real.pi,
        cotSinePolynomial n.succ.succ x) = Real.pi
      rw [cotSinePolynomial_succ_fun n.succ]
      have hP : IntervalIntegrable (cotSinePolynomial n.succ)
          volume 0 Real.pi :=
        (cotSinePolynomial_continuous n.succ).intervalIntegrable _ _
      have hc1 : IntervalIntegrable
          (fun x : ℝ => Real.cos (2 * (n.succ + 1) * x))
          volume 0 Real.pi :=
        (by fun_prop : Continuous
          (fun x : ℝ => Real.cos (2 * (n.succ + 1) * x))).intervalIntegrable _ _
      have hc2 : IntervalIntegrable
          (fun x : ℝ => Real.cos (2 * n.succ * x))
          volume 0 Real.pi :=
        (by fun_prop : Continuous
          (fun x : ℝ => Real.cos (2 * n.succ * x))).intervalIntegrable _ _
      have hz1 :
          (∫ x : ℝ in 0..Real.pi,
            Real.cos (2 * (n.succ + 1) * x)) = 0 := by
        convert integral_cos_two_nat_mul (n + 2) (by omega) using 1 <;>
          push_cast <;> ring
      have hz2 :
          (∫ x : ℝ in 0..Real.pi,
            Real.cos (2 * n.succ * x)) = 0 := by
        convert integral_cos_two_nat_mul (n + 1) (by omega) using 1 <;>
          push_cast <;> ring
      rw [intervalIntegral.integral_add (hP.add hc1) hc2,
        intervalIntegral.integral_add hP hc1, ih, hz1, hz2]
      ring

theorem log_sin_cos_truncated_integration_by_parts
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < Real.pi / 2) :
    (∫ x : ℝ in epsilon..Real.pi - epsilon,
        Real.log (Real.sin x) * Real.cos (2 * n * x)) =
      Real.log (Real.sin (Real.pi - epsilon)) *
          (Real.sin (2 * n * (Real.pi - epsilon)) / (2 * n)) -
        Real.log (Real.sin epsilon) *
          (Real.sin (2 * n * epsilon) / (2 * n)) -
        (2 * (n : ℝ))⁻¹ *
          (∫ x : ℝ in epsilon..Real.pi - epsilon,
            cotSinePolynomial n x) := by
  have hfreq : (2 * (n : ℝ)) ≠ 0 := by positivity
  have horder : epsilon ≤ Real.pi - epsilon := by
    linarith
  have hsin_pos : ∀ x ∈ [[epsilon, Real.pi - epsilon]],
      0 < Real.sin x := by
    intro x hx
    rw [uIcc_of_le horder] at hx
    exact Real.sin_pos_of_pos_of_lt_pi
      (lt_of_lt_of_le hepsilon hx.1) (by linarith [hx.2])
  have hu : ∀ x ∈ [[epsilon, Real.pi - epsilon]],
      HasDerivAt (fun y : ℝ => Real.log (Real.sin y))
        (Real.cos x / Real.sin x) x := by
    intro x hx
    exact (Real.hasDerivAt_sin x).log (hsin_pos x hx).ne'
  have hv : ∀ x ∈ [[epsilon, Real.pi - epsilon]],
      HasDerivAt (fun y : ℝ =>
          Real.sin ((2 * (n : ℝ)) * y) / (2 * (n : ℝ)))
        (Real.cos ((2 * (n : ℝ)) * x)) x := by
    intro x _
    have h := ((Real.hasDerivAt_sin ((2 * (n : ℝ)) * x)).comp x
      ((hasDerivAt_id x).const_mul (2 * (n : ℝ)))).div_const
        (2 * (n : ℝ))
    convert h using 1
    · funext y
      rfl
    · field_simp [hfreq]
  have hu_cont : ContinuousOn (fun x : ℝ => Real.cos x / Real.sin x)
      [[epsilon, Real.pi - epsilon]] := by
    intro x hx
    exact (Real.continuous_cos.continuousAt.div
      Real.continuous_sin.continuousAt (hsin_pos x hx).ne').continuousWithinAt
  have hu_int : IntervalIntegrable
      (fun x : ℝ => Real.cos x / Real.sin x)
      volume epsilon (Real.pi - epsilon) :=
    hu_cont.intervalIntegrable
  have hv_int : IntervalIntegrable
      (fun x : ℝ => Real.cos ((2 * (n : ℝ)) * x))
      volume epsilon (Real.pi - epsilon) :=
    (by fun_prop : Continuous
      (fun x : ℝ => Real.cos ((2 * (n : ℝ)) * x))).intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu_int hv_int
  have hcot :
      (∫ x : ℝ in epsilon..Real.pi - epsilon,
        (Real.cos x / Real.sin x) *
          (Real.sin ((2 * (n : ℝ)) * x) / (2 * (n : ℝ)))) =
        (2 * (n : ℝ))⁻¹ *
          (∫ x : ℝ in epsilon..Real.pi - epsilon,
            cotSinePolynomial n x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hsne : Real.sin x ≠ 0 := (hsin_pos x hx).ne'
    change (Real.cos x / Real.sin x) *
        (Real.sin ((2 * (n : ℝ)) * x) / (2 * (n : ℝ))) =
      (2 * (n : ℝ))⁻¹ * cotSinePolynomial n x
    rw [cotSinePolynomial_eq n x hsne]
    field_simp [hfreq, hsne]
  rw [hcot] at hparts
  convert hparts using 1 <;> push_cast <;> ring

theorem tendsto_log_sin_mul_sin_nat_div
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun epsilon : ℝ =>
        Real.log (Real.sin epsilon) *
          (Real.sin (2 * n * epsilon) / (2 * n)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hfreq : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hid0 : Tendsto (fun epsilon : ℝ => epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left inf_le_left
  have hevent : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      0 < epsilon ∧ epsilon < Real.pi := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)]
      with epsilon hpos hpi
    exact ⟨hpos, hpi⟩
  have hsin0 : Tendsto (fun epsilon : ℝ => Real.sin epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.sin_zero, Function.comp_def] using
      Real.continuous_sin.continuousAt.tendsto.comp hid0
  have hsinpos : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      Real.sin epsilon ∈ Ioi (0 : ℝ) := by
    filter_upwards [hevent] with epsilon hepsilon
    exact Real.sin_pos_of_pos_of_lt_pi hepsilon.1 hepsilon.2
  have hsinWithin : Tendsto (fun epsilon : ℝ => Real.sin epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ hsin0 hsinpos
  have hbase := tendsto_log_mul_rpow_nhdsGT_zero
    (r := (1 : ℝ)) zero_lt_one
  simp only [Real.rpow_one] at hbase
  have hlogsin : Tendsto (fun epsilon : ℝ =>
      Real.log (Real.sin epsilon) * Real.sin epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def] using hbase.comp hsinWithin
  have hfreq0 : Tendsto (fun epsilon : ℝ => (2 * (n : ℝ)) * epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hid0.const_mul (2 * (n : ℝ)) using 1 <;> ring
  have hsincFreq : Tendsto (fun epsilon : ℝ =>
      Real.sinc ((2 * (n : ℝ)) * epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using
      (Real.continuous_sinc.tendsto 0).comp hfreq0
  have hsinc : Tendsto (fun epsilon : ℝ => Real.sinc epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using
      (Real.continuous_sinc.tendsto 0).comp hid0
  have hratio : Tendsto (fun epsilon : ℝ =>
      Real.sinc ((2 * (n : ℝ)) * epsilon) / Real.sinc epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    change Tendsto
      ((fun epsilon : ℝ => Real.sinc ((2 * (n : ℝ)) * epsilon)) /
        (fun epsilon : ℝ => Real.sinc epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 1)
    simpa only [div_one] using hsincFreq.div hsinc one_ne_zero
  have hproduct := hlogsin.mul hratio
  have heq : (fun epsilon : ℝ =>
      (Real.log (Real.sin epsilon) * Real.sin epsilon) *
        (Real.sinc ((2 * (n : ℝ)) * epsilon) /
          Real.sinc epsilon)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun epsilon : ℝ =>
        Real.log (Real.sin epsilon) *
          (Real.sin (2 * n * epsilon) / (2 * n)) := by
    filter_upwards [hevent] with epsilon hepsilon
    have he0 : epsilon ≠ 0 := hepsilon.1.ne'
    have hfe0 : (2 * (n : ℝ)) * epsilon ≠ 0 :=
      mul_ne_zero hfreq he0
    have hs0 : Real.sin epsilon ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hepsilon.1 hepsilon.2).ne'
    rw [Real.sinc_of_ne_zero hfe0, Real.sinc_of_ne_zero he0]
    push_cast
    field_simp [hfreq, he0, hs0]
  have hproduct' : Tendsto (fun epsilon : ℝ =>
      (Real.log (Real.sin epsilon) * Real.sin epsilon) *
        (Real.sinc ((2 * (n : ℝ)) * epsilon) /
          Real.sinc epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hproduct
  exact hproduct'.congr' heq

/-- Every nonzero cosine coefficient of `log (sin x)` on `(0, π)`.
This is proved by genuine endpoint truncation and integration by parts. -/
theorem integral_log_sin_mul_cos_two_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in 0..Real.pi,
      Real.log (Real.sin x) * Real.cos (2 * n * x)) =
        -(Real.pi / (2 * n)) := by
  have hfreq : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hmain := tendsto_truncated_intervalIntegral
    (intervalIntegrable_log_sin_mul_cos n)
  have hleft := tendsto_log_sin_mul_sin_nat_div n hn
  have hright : Tendsto (fun epsilon : ℝ =>
      Real.log (Real.sin (Real.pi - epsilon)) *
        (Real.sin (2 * n * (Real.pi - epsilon)) / (2 * n)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hneg := hleft.neg
    have hevent : (fun epsilon : ℝ =>
        -(Real.log (Real.sin epsilon) *
          (Real.sin (2 * n * epsilon) / (2 * n)))) =ᶠ[
            𝓝[>] (0 : ℝ)]
        fun epsilon : ℝ =>
          Real.log (Real.sin (Real.pi - epsilon)) *
            (Real.sin (2 * n * (Real.pi - epsilon)) / (2 * n)) := by
      filter_upwards with epsilon
      rw [Real.sin_pi_sub]
      have htrig :
          Real.sin (2 * (n : ℝ) * (Real.pi - epsilon)) =
            -Real.sin (2 * (n : ℝ) * epsilon) := by
        convert Real.sin_nat_mul_two_pi_sub
          (2 * (n : ℝ) * epsilon) n using 1 <;> push_cast <;> ring
      push_cast
      rw [htrig]
      ring
    have hneg' : Tendsto (fun epsilon : ℝ =>
        -(Real.log (Real.sin epsilon) *
          (Real.sin (2 * n * epsilon) / (2 * n))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hneg
    exact hneg'.congr' hevent
  have hpolyInt : IntervalIntegrable (cotSinePolynomial n)
      volume 0 Real.pi :=
    (cotSinePolynomial_continuous n).intervalIntegrable _ _
  have hpoly := tendsto_truncated_intervalIntegral hpolyInt
  have hn_pred : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn
  have hpolyFull :
      (∫ x : ℝ in 0..Real.pi, cotSinePolynomial n x) = Real.pi := by
    have h := cotSinePolynomial_intervalIntegral (n - 1)
    rw [hn_pred] at h
    exact h
  rw [hpolyFull] at hpoly
  have hscaled : Tendsto (fun epsilon : ℝ =>
      (2 * (n : ℝ))⁻¹ *
        (∫ x : ℝ in epsilon..Real.pi - epsilon,
          cotSinePolynomial n x))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 * (n : ℝ))⁻¹ * Real.pi)) := by
    exact hpoly.const_mul (2 * (n : ℝ))⁻¹
  have hrhs := (hright.sub hleft).sub hscaled
  have hrhs' : Tendsto (fun epsilon : ℝ =>
      Real.log (Real.sin (Real.pi - epsilon)) *
          (Real.sin (2 * n * (Real.pi - epsilon)) / (2 * n)) -
        Real.log (Real.sin epsilon) *
          (Real.sin (2 * n * epsilon) / (2 * n)) -
        (2 * (n : ℝ))⁻¹ *
          (∫ x : ℝ in epsilon..Real.pi - epsilon,
            cotSinePolynomial n x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / (2 * n)))) := by
    convert hrhs using 1 <;> push_cast <;> field_simp [hfreq] <;> ring
  have heq : (fun epsilon : ℝ =>
      ∫ x : ℝ in epsilon..Real.pi - epsilon,
        Real.log (Real.sin x) * Real.cos (2 * n * x)) =ᶠ[
          𝓝[>] (0 : ℝ)]
      fun epsilon : ℝ =>
        Real.log (Real.sin (Real.pi - epsilon)) *
            (Real.sin (2 * n * (Real.pi - epsilon)) / (2 * n)) -
          Real.log (Real.sin epsilon) *
            (Real.sin (2 * n * epsilon) / (2 * n)) -
          (2 * (n : ℝ))⁻¹ *
            (∫ x : ℝ in epsilon..Real.pi - epsilon,
              cotSinePolynomial n x) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 2))]
      with epsilon he0 hehalf
    exact log_sin_cos_truncated_integration_by_parts
      n hn epsilon he0 hehalf
  have hmain' := hmain.congr' heq
  exact tendsto_nhds_unique hmain' hrhs'

end HBL
