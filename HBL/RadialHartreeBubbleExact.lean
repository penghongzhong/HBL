import HBL.RadialHartreePotential
import HBL.RadialHartreeBubbleBound
import HBL.AffineTailLogIntegralEvaluation
import HBL.MonopoleTailCharge

/-!
Exact evaluation of the genuine radial Hartree potential of the fourth
power of the manuscript bubble. All integrals are ordinary absolutely
convergent Lebesgue integrals.

The logarithmic antiderivative is continuous at the diagonal because its
singular part has the explicit form `(x-r) * log (x-r)`. We apply FTC on
the two separate intervals `0..r` and `r..R`. Thus no Cauchy kernel is
asserted to be Lebesgue integrable and no pole boundary is discarded.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The scalar logarithmic density for the actual fourth-power bubble. -/
def bubbleLogDensity (r x : ℝ) : ℝ :=
  x / (1 + x ^ 2) ^ 2 * hartreeRadialLog r x

/-- Primitive of the nonsingular rational weight. -/
def bubbleLogWeightPrimitive (x : ℝ) : ℝ :=
  -(1 + x ^ 2)⁻¹ / 2

/-- A combined antiderivative with a removable logarithmic singularity. -/
def bubbleLogPrimitive (r x : ℝ) : ℝ :=
  (x ^ 2 - r ^ 2) / (2 * (1 + r ^ 2) * (1 + x ^ 2)) *
    (Real.log (r + x) - Real.log (r - x)) +
    r / (1 + r ^ 2) * Real.arctan x

theorem bubbleLogDensity_eq_actual (r x : ℝ) :
    bubbleLogDensity r x = x * hartreeRadialLog r x * bubble x ^ 4 := by
  have hfour : bubble x ^ 4 = ((1 + x ^ 2) ^ 2)⁻¹ := by
    rw [show bubble x ^ 4 = (bubble x ^ 2) ^ 2 by ring, bubble_sq, inv_pow]
  rw [bubbleLogDensity, hfour]
  ring

/-- Local absolute convergence includes the diagonal. -/
theorem bubbleLogDensity_intervalIntegrable (r a b : ℝ) :
    IntervalIntegrable (bubbleLogDensity r) volume a b := by
  have hc : Continuous (fun x : ℝ => x / (1 + x ^ 2) ^ 2) := by
    fun_prop (discharger := intro; positivity)
  have hi := (splitRadialLog_intervalIntegrable r a b).mul_continuousOn hc.continuousOn
  apply hi.congr_ae
  apply ae_restrict_of_ae
  filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ r by simp [ae_iff],
    show ∀ᵐ x : ℝ ∂volume, x ≠ -r by simp [ae_iff]] with x hx hx'
  unfold bubbleLogDensity hartreeRadialLog
  rw [radialLog_ratio_eq_sub r x (by intro h; apply hx'; linarith)
    (by intro h; apply hx; linarith)]
  ring

/-- Global absolute convergence follows by domination by the already
verified bubble-squared row, before any primitive or limit is used. -/
theorem bubbleLogDensity_integrableOn_pos {r : ℝ} (hr : 0 < r) :
    IntegrableOn (bubbleLogDensity r) (Ioi 0) := by
  have hm : Measurable (bubbleLogDensity r) := by
    unfold bubbleLogDensity hartreeRadialLog
    fun_prop
  apply (radialHartreeBubble_integrable_bound hr).1.mono'
    hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have hl := hartreeRadialLog_nonneg r x hr hx0
  have hb : 0 < (1 + x ^ 2 : ℝ) := by positivity
  have hweight : x / (1 + x ^ 2) ^ 2 ≤ x / (1 + x ^ 2) := by
    apply div_le_div_of_nonneg_left hx0.le hb
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  rw [bubbleLogDensity, Real.norm_eq_abs, abs_of_nonneg (by positivity), bubble_sq]
  calc
    x / (1 + x ^ 2) ^ 2 * hartreeRadialLog r x ≤
        x / (1 + x ^ 2) * hartreeRadialLog r x :=
      mul_le_mul_of_nonneg_right hweight hl
    _ = x * hartreeRadialLog r x * (1 + x ^ 2)⁻¹ := by ring

theorem bubbleLogWeightPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt bubbleLogWeightPrimitive (x / (1 + x ^ 2) ^ 2) x := by
  have hA : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)
    convert h using 1
    · funext y
      simp
    · norm_num
  have hAne : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have h := ((hA.inv hAne).neg).div_const 2
  convert h using 1 <;>
    (first | rfl | (field_simp [hAne] <;> ring))

/-- This identity is used only for differentiation away from the poles
and the far-end limit; it is not an assertion of PV integrability. -/
theorem bubbleLogPrimitive_eq_pv (r x : ℝ) (hr : r ≠ 0) :
    bubbleLogPrimitive r x =
      bubbleLogWeightPrimitive x * (Real.log (r + x) - Real.log (r - x)) +
        r / (1 + r ^ 2) * (Real.arctan x + pvRationalPrimitive r x) := by
  unfold bubbleLogPrimitive bubbleLogWeightPrimitive pvRationalPrimitive
  field_simp [hr, (by positivity : (1 + x ^ 2 : ℝ) ≠ 0),
    (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)]
  ring

theorem bubbleLogPrimitive_hasDerivAt (r x : ℝ) (hr : r ≠ 0)
    (hp : r + x ≠ 0) (hm : r - x ≠ 0) :
    HasDerivAt (bubbleLogPrimitive r) (bubbleLogDensity r x) x := by
  have hsep : r ^ 2 - x ^ 2 ≠ 0 := by
    intro hz
    have hprod : (r + x) * (r - x) = 0 := by nlinarith [hz]
    exact (mul_ne_zero hp hm) hprod
  have hlog := splitRadialLog_hasDerivAt r x hp hm
  have hprod := (bubbleLogWeightPrimitive_hasDerivAt x).mul hlog
  have hregular := ((Real.hasDerivAt_arctan' x).add
    (pvRationalPrimitive_hasDerivAt r x hr hp hm)).const_mul (r / (1 + r ^ 2))
  have h := hprod.add hregular
  convert h using 1
  · funext y
    exact bubbleLogPrimitive_eq_pv r y hr
  · unfold bubbleLogDensity hartreeRadialLog bubbleLogWeightPrimitive
    rw [radialLog_ratio_eq_sub r x hp hm]
    field_simp [hsep, (by positivity : (1 + x ^ 2 : ℝ) ≠ 0),
      (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)]
    ring

/-- The diagonal's singular term is exactly a continuous multiple of
`(x-r) log (x-r)`, making the zero endpoint contribution explicit. -/
theorem bubbleLogPrimitive_eq_mul_log (r x : ℝ) :
    bubbleLogPrimitive r x =
      (x + r) / (2 * (1 + r ^ 2) * (1 + x ^ 2)) *
        ((x - r) * Real.log (r + x) - (x - r) * Real.log (x - r)) +
        r / (1 + r ^ 2) * Real.arctan x := by
  have hlog : Real.log (r - x) = Real.log (x - r) := by
    rw [show r - x = -(x - r) by ring, Real.log_neg_eq_log]
  unfold bubbleLogPrimitive
  rw [hlog]
  field_simp [(by positivity : (1 + x ^ 2 : ℝ) ≠ 0),
    (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)]
  ring

/-- Continuity includes `x=r`; this is the epsilon-log-epsilon endpoint
argument and does not assert differentiability at the logarithmic pole. -/
theorem bubbleLogPrimitive_continuousAt {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    ContinuousAt (bubbleLogPrimitive r) x := by
  have hcoef : Continuous (fun y : ℝ =>
      (y + r) / (2 * (1 + r ^ 2) * (1 + y ^ 2))) := by
    fun_prop (discharger := intro; positivity)
  have hlog : ContinuousAt (fun y : ℝ => Real.log (r + y)) x :=
    (continuous_const.add continuous_id).continuousAt.log
      (by change r + x ≠ 0; linarith)
  have hfirst : ContinuousAt (fun y : ℝ => (y - r) * Real.log (r + y)) x :=
    (continuous_id.sub continuous_const).continuousAt.mul hlog
  have hsing : Continuous (fun y : ℝ => (y - r) * Real.log (y - r)) :=
    Real.continuous_mul_log.comp (continuous_id.sub continuous_const)
  have hlast : Continuous (fun y : ℝ => r / (1 + r ^ 2) * Real.arctan y) :=
    Real.continuous_arctan.const_mul _
  have heq : bubbleLogPrimitive r = fun y : ℝ =>
      (y + r) / (2 * (1 + r ^ 2) * (1 + y ^ 2)) *
        ((y - r) * Real.log (r + y) - (y - r) * Real.log (y - r)) +
        r / (1 + r ^ 2) * Real.arctan y :=
    funext (bubbleLogPrimitive_eq_mul_log r)
  rw [heq]
  exact (hcoef.continuousAt.mul (hfirst.sub hsing.continuousAt)).add hlast.continuousAt

@[simp] theorem bubbleLogPrimitive_zero (r : ℝ) : bubbleLogPrimitive r 0 = 0 := by
  simp [bubbleLogPrimitive]

@[simp] theorem bubbleLogPrimitive_diagonal (r : ℝ) :
    bubbleLogPrimitive r r = r / (1 + r ^ 2) * Real.arctan r := by
  simp [bubbleLogPrimitive]

/-- FTC is applied separately on both sides of the diagonal. The two
finite diagonal endpoint values cancel by proved continuity. -/
theorem bubbleLogDensity_integral_finite {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    (∫ x in (0 : ℝ)..R, bubbleLogDensity r x) = bubbleLogPrimitive r R := by
  have hleft : (∫ x in (0 : ℝ)..r, bubbleLogDensity r x) =
      bubbleLogPrimitive r r - bubbleLogPrimitive r 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := bubbleLogPrimitive r) (f' := bubbleLogDensity r) hr.le
    · intro x hx
      exact (bubbleLogPrimitive_continuousAt hr hx.1).continuousWithinAt
    · intro x hx
      exact bubbleLogPrimitive_hasDerivAt r x hr.ne'
        (by linarith [hx.1]) (by linarith [hx.2])
    · exact bubbleLogDensity_intervalIntegrable r 0 r
  have hright : (∫ x in r..R, bubbleLogDensity r x) =
      bubbleLogPrimitive r R - bubbleLogPrimitive r r := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := bubbleLogPrimitive r) (f' := bubbleLogDensity r) hR.le
    · intro x hx
      exact (bubbleLogPrimitive_continuousAt hr (by linarith [hx.1])).continuousWithinAt
    · intro x hx
      exact bubbleLogPrimitive_hasDerivAt r x hr.ne'
        (by linarith [hx.1]) (by linarith [hx.1])
    · exact bubbleLogDensity_intervalIntegrable r r R
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (bubbleLogDensity_intervalIntegrable r 0 r)
    (bubbleLogDensity_intervalIntegrable r r R)
  rw [hleft, hright, bubbleLogPrimitive_zero] at hadd
  linarith

/-- The entire far endpoint is evaluated, including its logarithmic term. -/
theorem bubbleLogPrimitive_tendsto_atTop {r : ℝ} (hr : 0 < r) :
    Tendsto (bubbleLogPrimitive r) atTop
      (𝓝 (Real.pi * r / (2 * (1 + r ^ 2)))) := by
  have hQ : Tendsto bubbleLogWeightPrimitive atTop (𝓝 0) := by
    have h := inv_one_add_sq_tendsto_zero.neg.div_const 2
    change Tendsto (fun x : ℝ => -(1 + x ^ 2)⁻¹ / 2) atTop (𝓝 0)
    simpa only [neg_zero, zero_div] using h
  have hlog0 := (pvRationalPrimitive_tendsto_zero_atTop r hr).const_mul (2 * r)
  have hlog : Tendsto
      (fun R : ℝ => Real.log (r + R) - Real.log (r - R)) atTop (𝓝 0) := by
    convert hlog0 using 1
    · funext R
      unfold pvRationalPrimitive
      field_simp [hr.ne']
    · simp
  have ha : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have h := (hQ.mul hlog).add
    ((ha.add (pvRationalPrimitive_tendsto_zero_atTop r hr)).const_mul (r / (1 + r ^ 2)))
  convert h using 1
  · funext R
    exact bubbleLogPrimitive_eq_pv r R hr.ne'
  · congr 1
    field_simp [(by positivity : (1 + r ^ 2 : ℝ) ≠ 0)] <;> ring

/-- Exact value of the absolutely convergent scalar radial integral. -/
theorem bubbleLogDensity_integral_eq {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), bubbleLogDensity r x) =
      Real.pi * r / (2 * (1 + r ^ 2)) := by
  have hLebesgue := intervalIntegral_tendsto_integral_Ioi 0
    (bubbleLogDensity_integrableOn_pos hr) (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hvalue : Tendsto
      (fun R : ℝ => ∫ x in (0 : ℝ)..R, bubbleLogDensity r x) atTop
      (𝓝 (Real.pi * r / (2 * (1 + r ^ 2)))) := by
    apply (bubbleLogPrimitive_tendsto_atTop hr).congr'
    filter_upwards [eventually_gt_atTop r] with R hR
    exact (bubbleLogDensity_integral_finite hr hR).symm
  exact tendsto_nhds_unique hLebesgue hvalue

/-- The genuine Hartree density is absolutely integrable. -/
theorem radialHartreeBubble_four_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => x * hartreeRadialLog r x * bubble x ^ 4) (Ioi 0) := by
  refine (bubbleLogDensity_integrableOn_pos hr).congr ?_
  exact Filter.Eventually.of_forall (bubbleLogDensity_eq_actual r)

/-- Before substituting the manuscript normalization, the exact constant
is `pi^2 * hartreeKappa`; the original potential definition is used. -/
theorem radialHartreePotential_bubble_four_exact {r : ℝ} (hr : 0 < r) :
    radialHartreePotential (fun x => bubble x ^ 4) r =
      Real.pi ^ 2 * hartreeKappa * bubble r ^ 2 := by
  have hi : (∫ x in Ioi (0 : ℝ), x * hartreeRadialLog r x * bubble x ^ 4) =
      Real.pi * r / (2 * (1 + r ^ 2)) := by
    simpa only [bubbleLogDensity_eq_actual] using bubbleLogDensity_integral_eq hr
  rw [radialHartreePotential, hi, bubble_sq]
  field_simp [hr.ne', (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)]

/-- With the project's actual `hartreeKappa = 3 / pi^2`, the fourth-power
bubble potential is exactly `3 W^2` at every positive radius. -/
theorem radialHartreePotential_bubble_four {r : ℝ} (hr : 0 < r) :
    radialHartreePotential (fun x => bubble x ^ 4) r = 3 * bubble r ^ 2 := by
  rw [radialHartreePotential_bubble_four_exact hr]
  unfold hartreeKappa
  field_simp [Real.pi_ne_zero]

end HBL.Modulation.Monopole
