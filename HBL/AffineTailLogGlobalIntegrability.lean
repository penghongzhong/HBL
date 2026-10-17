import HBL.AffineTailLogFarBound
import HBL.AffineTailRationalIntegrability
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Global absolute integrability of the logarithmic density in the radial
Hartree reduction.  Local integrability across the diagonal is combined
with the quantitative far-field estimate.
-/

noncomputable section

open Set MeasureTheory
open Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- The logarithmic density is measurable, including at its harmless
pointwise representatives on the two zeros of the logarithm's argument. -/
theorem affineLogDensity_measurable (r : ℝ) :
    Measurable (affineLogDensity r) := by
  unfold affineLogDensity
  fun_prop

/-- The rational coefficient is bounded by the positive squared-denominator
kernel on the far half-line. -/
theorem affineRationalFactor_abs_le (rho : ℝ) (hρ : 0 ≤ rho) :
    |rho * (1 - rho ^ 2) / (2 * (1 + rho ^ 2) ^ 3)| ≤
      rho / (2 * (1 + rho ^ 2) ^ 2) := by
  have hbase : 0 < (1 + rho ^ 2 : ℝ) := by positivity
  have habs : |1 - rho ^ 2| ≤ 1 + rho ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg rho]
  rw [abs_div, abs_mul, abs_of_nonneg hρ,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * (1 + rho ^ 2) ^ 3)]
  apply (div_le_div_iff₀
    (by positivity : (0 : ℝ) < 2 * (1 + rho ^ 2) ^ 3)
    (by positivity : (0 : ℝ) < 2 * (1 + rho ^ 2) ^ 2)).2
  nlinarith [mul_le_mul_of_nonneg_left habs hρ]

/-- Beyond twice the observation radius, the complete logarithmic density
is dominated by an absolutely integrable rational kernel. -/
theorem affineLogDensity_norm_far_le (r rho : ℝ)
    (hr : 0 < r) (hρ : 2 * r ≤ rho) :
    ‖affineLogDensity r rho‖ ≤
      2 * r * ((1 + rho ^ 2) ^ 2)⁻¹ := by
  have hρpos : 0 < rho := by linarith
  rcases radialLog_far_inv_bound r rho hr hρ with ⟨hlog0, hlog⟩
  rw [affineLogDensity, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hlog0]
  calc
    |rho * (1 - rho ^ 2) / (2 * (1 + rho ^ 2) ^ 3)| *
          Real.log ((r + rho) / |r - rho|) ≤
        (rho / (2 * (1 + rho ^ 2) ^ 2)) *
          Real.log ((r + rho) / |r - rho|) := by
            gcongr
            exact affineRationalFactor_abs_le rho hρpos.le
    _ ≤ (rho / (2 * (1 + rho ^ 2) ^ 2)) * (4 * r / rho) := by
          gcongr
    _ = 2 * r * ((1 + rho ^ 2) ^ 2)⁻¹ := by
          field_simp [ne_of_gt hρpos, (by positivity : (1 + rho ^ 2 : ℝ) ≠ 0)]
          <;> ring

/-- The original ratio-log density is locally integrable, because it agrees
almost everywhere with the difference of the two translated logarithms. -/
theorem affineLogDensity_intervalIntegrable (r a b : ℝ) :
    IntervalIntegrable (affineLogDensity r) volume a b := by
  apply (splitAffineLogDensity_intervalIntegrable r a b).congr_ae
  apply ae_restrict_of_ae
  filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ r by simp [ae_iff],
    show ∀ᵐ x : ℝ ∂volume, x ≠ -r by simp [ae_iff]] with x hx hx'
  unfold affineLogDensity
  rw [radialLog_ratio_eq_sub r x (by intro h; apply hx'; linarith)
    (by intro h; apply hx; linarith)]
  ring

/-- Absolute Lebesgue integrability on the whole positive half-line. -/
theorem affineLogDensity_integrableOn_pos (r : ℝ) (hr : 0 < r) :
    IntegrableOn (affineLogDensity r) (Ioi 0) := by
  have hlocal : IntegrableOn (affineLogDensity r) (Ioc 0 (2 * r)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
      (affineLogDensity_intervalIntegrable r 0 (2 * r))
  have hdom : IntegrableOn
      (fun x : ℝ => 2 * r * ((1 + x ^ 2) ^ 2)⁻¹) (Ioi (2 * r)) :=
    (second_rational_integrable.const_mul (2 * r)).integrableOn
  have hfar : IntegrableOn (affineLogDensity r) (Ioi (2 * r)) := by
    apply hdom.mono' (affineLogDensity_measurable r).aestronglyMeasurable.restrict
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ (fun x hx => affineLogDensity_norm_far_le r x hr hx.le))
  have hset : Ioc 0 (2 * r) ∪ Ioi (2 * r) = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨h, _⟩ | h) <;> linarith
    · intro h
      by_cases hx : x ≤ 2 * r
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  rw [← hset]
  exact hlocal.union hfar

/-- The finite upper-cutoff integrals converge to the Lebesgue integral. -/
theorem affineLogDensity_integral_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, affineLogDensity r x)
      atTop (𝓝 (affineLogIntegral r)) := by
  exact intervalIntegral_tendsto_integral_Ioi 0
    (affineLogDensity_integrableOn_pos r hr) tendsto_id

/-- Removing a shrinking symmetric interval loses no logarithmic mass. -/
theorem affineLogDensity_gap_integral_tendsto_zero (r : ℝ) :
    Tendsto (fun e : ℝ => ∫ x in (r - e)..(r + e), affineLogDensity r x)
      (𝓝 0) (𝓝 0) := by
  have hc := intervalIntegral.continuous_primitive
    (affineLogDensity_intervalIntegrable r) r
  have hm := (hc.comp (continuous_const.sub continuous_id :
    Continuous (fun e : ℝ => r - e))).continuousAt.tendsto (x := (0 : ℝ))
  have hp := (hc.comp (continuous_const.add continuous_id :
    Continuous (fun e : ℝ => r + e))).continuousAt.tendsto (x := (0 : ℝ))
  have hlim := hp.sub hm
  simp only [Function.comp_def, Pi.add_apply, Pi.sub_apply,
    add_zero, sub_zero, sub_self] at hlim
  apply hlim.congr'
  filter_upwards with e
  exact intervalIntegral.integral_interval_sub_left
    (affineLogDensity_intervalIntegrable r r (r + e))
    (affineLogDensity_intervalIntegrable r r (r - e))

/-- Symmetric exclusion and an infinite upper cutoff recover the same
Lebesgue integral along every joint limiting path. -/
theorem affineLogDensity_cutoff_tendsto {α : Type*} (l : Filter α)
    (r : ℝ) (hr : 0 < r) (R e : α → ℝ)
    (hR : Tendsto R l atTop) (he : Tendsto e l (𝓝 0)) :
    Tendsto (fun i =>
      (∫ x in (0 : ℝ)..(r - e i), affineLogDensity r x) +
      (∫ x in (r + e i)..R i, affineLogDensity r x))
      l (𝓝 (affineLogIntegral r)) := by
  have hlim := ((affineLogDensity_integral_tendsto r hr).comp hR).sub
    ((affineLogDensity_gap_integral_tendsto_zero r).comp he)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards with i
  have hid := intervalIntegral.integral_interval_add_interval_comm
    (affineLogDensity_intervalIntegrable r 0 (r - e i))
    (affineLogDensity_intervalIntegrable r (r + e i) (R i))
    (affineLogDensity_intervalIntegrable r 0 (r + e i))
  rw [intervalIntegral.integral_symm (r - e i) (r + e i)] at hid
  simpa only [Function.comp_def, sub_eq_add_neg] using hid.symm

end HBL.Modulation.AffineTail
