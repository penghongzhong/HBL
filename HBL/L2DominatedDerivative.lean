import HBL.TransportedTestTailUniform
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
A dominated strong-differentiation lemma for real L2 families.

This is the functional-analytic step needed to upgrade pointwise
differentiation of the transported radial test tails to differentiation
in the Hilbert L2 norm.  The proof is entirely in Mathlib: dominated
convergence is applied to the squared norm of the difference quotient,
and the resulting eLpNorm convergence is converted to convergence in L2.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace HBL.Modulation

/-- Dominated pointwise convergence upgrades to strong convergence in real L2. -/
theorem realLp2_tendsto_dominated
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → α → ℝ) (g : α → ℝ)
    (hF : ∀ i, MemLp (F i) 2 μ) (hg : MemLp g 2 μ)
    (w : α → ℝ) (hw : Integrable (fun y => w y ^ 2) μ)
    (hb : ∀ᶠ i in l, ∀ᵐ y ∂μ, ‖F i y - g y‖ ≤ w y)
    (hlim : ∀ᵐ y ∂μ, Tendsto (fun i => F i y) l (𝓝 (g y))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hg.toLp g)) := by
  have hint : Tendsto (fun i => ∫ y, ‖F i y - g y‖ ^ 2 ∂μ) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (F := fun i y => ‖F i y - g y‖ ^ 2)
      (f := fun _ => (0 : ℝ)) (fun y => w y ^ 2)
      (Eventually.of_forall fun i => by
        have hi :=
          ((hF i).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2
        change AEStronglyMeasurable (fun y => ‖F i y - g y‖ ^ 2) μ at hi
        exact hi)
      (by
        filter_upwards [hb] with i hi
        filter_upwards [hi] with y hiy
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hiy 2)
      hw
      (by
        filter_upwards [hlim] with y hy
        simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
          ((hy.sub_const (g y)).norm.pow 2))
    simpa only [integral_zero] using hh
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF g hg).mpr
  have he (i : ι) :
      eLpNorm (F i - g) 2 μ =
        ENNReal.ofReal (Real.sqrt (∫ y, ‖F i y - g y‖ ^ 2 ∂μ)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num) ((hF i).sub hg)]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp hint)
  simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] using hh

/-- If the pointwise slopes converge to a derivative and are dominated in L2,
then the corresponding L2-valued map has that strong derivative. -/
theorem realLp2_hasDerivAt
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℝ → α → ℝ) (g : α → ℝ) (t : ℝ)
    (hF : ∀ s, MemLp (F s) 2 μ) (hg : MemLp g 2 μ)
    (w : α → ℝ) (hw : Integrable (fun y => w y ^ 2) μ)
    (hb : ∀ᶠ s in 𝓝[≠] t,
      ∀ᵐ y ∂μ, ‖slope (fun r => F r y) t s - g y‖ ≤ w y)
    (hd : ∀ᵐ y ∂μ, HasDerivAt (fun s => F s y) (g y) t) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hg.toLp g) t := by
  let S := fun s y => slope (fun r => F r y) t s
  have hS (s : ℝ) : MemLp (S s) 2 μ :=
    ((hF s).sub (hF t)).const_smul (s - t)⁻¹
  have hlim := realLp2_tendsto_dominated S g hS hg w hw hb
    (hd.mono fun _ hy => hy.tendsto_slope)
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hlim using 1
  funext s
  change (s - t)⁻¹ • ((hF s).toLp (F s) - (hF t).toLp (F t)) =
    (hS s).toLp (S s)
  rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul]
  rfl

/-- A practical version: an L2-integrable increment bound and a matching
pointwise derivative bound imply strong L2 differentiability. -/
theorem realLp2_hasDerivAt_of_increment_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℝ → α → ℝ) (g : α → ℝ) (t : ℝ)
    (hF : ∀ s, MemLp (F s) 2 μ) (hg : MemLp g 2 μ)
    (w : α → ℝ) (hw : Integrable (fun y => w y ^ 2) μ)
    (hb : ∀ᶠ s in 𝓝 t,
      ∀ᵐ y ∂μ, ‖F s y - F t y‖ ≤ |s - t| * w y)
    (hgb : ∀ᵐ y ∂μ, ‖g y‖ ≤ w y)
    (hd : ∀ᵐ y ∂μ, HasDerivAt (fun s => F s y) (g y) t) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hg.toLp g) t := by
  have hslope :
      ∀ᶠ s in 𝓝[≠] t,
        ∀ᵐ y ∂μ, ‖slope (fun r => F r y) t s‖ ≤ w y := by
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with s hs hst
    filter_upwards [hs] with y hsy
    have hne : s - t ≠ 0 := sub_ne_zero.mpr hst
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv]
    calc
      |s - t|⁻¹ * ‖F s y - F t y‖
          ≤ |s - t|⁻¹ * (|s - t| * w y) :=
        mul_le_mul_of_nonneg_left hsy (by positivity)
      _ = w y := by
        rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hne), one_mul]
  have hdiff :
      ∀ᶠ s in 𝓝[≠] t,
        ∀ᵐ y ∂μ,
          ‖slope (fun r => F r y) t s - g y‖ ≤ 2 * w y := by
    filter_upwards [hslope] with s hs
    filter_upwards [hs, hgb] with y hsy hgy
    exact (norm_sub_le _ _).trans (by linarith only [hsy, hgy])
  apply realLp2_hasDerivAt F g t hF hg (fun y => 2 * w y)
  · simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      hw.const_mul 4
  · exact hdiff
  · exact hd

end HBL.Modulation
