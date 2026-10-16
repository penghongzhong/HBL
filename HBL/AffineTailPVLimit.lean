import HBL.AffineTailPVFiniteIntegral

/-!
Vanishing of the simple-pole principal-value term.

For r>0, the primitive of 1/(r^2-rho^2) tends to zero at +infinity.
Combining this with the exact finite split identity shows that, for each
fixed symmetric gap e, the outer-radius limit is precisely the singular
boundary gap.  The latter was already proved to vanish as e -> 0.

Thus the simple Cauchy-kernel contribution has zero iterated principal
value, leaving only the two absolutely integrable rational terms.
-/

noncomputable section

open Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- The Cauchy-kernel primitive vanishes at the far endpoint. -/
theorem pvRationalPrimitive_tendsto_zero_atTop
    (r : ℝ) (hr : 0 < r) :
    Tendsto (pvRationalPrimitive r) atTop (𝓝 (0 : ℝ)) := by
  have hinv :
      Tendsto (fun rho : ℝ => rho⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hx :
      Tendsto (fun rho : ℝ => r * rho⁻¹)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hinv.const_mul r
  have hnum :
      Tendsto (fun rho : ℝ => r * rho⁻¹ + 1)
        atTop (𝓝 (1 : ℝ)) := by
    simpa using hx.add tendsto_const_nhds
  have hden :
      Tendsto (fun rho : ℝ => r * rho⁻¹ - 1)
        atTop (𝓝 (-1 : ℝ)) := by
    simpa using hx.sub tendsto_const_nhds
  have hratio0 :
      Tendsto
        (fun rho : ℝ =>
          (r * rho⁻¹ + 1) / (r * rho⁻¹ - 1))
        atTop (𝓝 (-1 : ℝ)) := by
    have h := hnum.div hden (by norm_num : (-1 : ℝ) ≠ 0)
    simpa using h
  have hratio :
      Tendsto (fun rho : ℝ => (r + rho) / (r - rho))
        atTop (𝓝 (-1 : ℝ)) := by
    apply hratio0.congr'
    filter_upwards [eventually_gt_atTop (max r 0 + 1)] with rho hρ
    have hρpos : 0 < rho := by
      have h0 : 0 ≤ max r 0 := le_max_right _ _
      linarith
    have hρ0 : rho ≠ 0 := ne_of_gt hρpos
    have hm : r - rho ≠ 0 := by
      have : r < rho := lt_of_le_of_lt (le_max_left r 0) (by linarith)
      linarith
    have hs : r * rho⁻¹ - 1 ≠ 0 := by
      intro hz
      have hz' : r = rho := by
        apply (eq_div_iff hρ0).mp
        change r / rho = 1
        simpa [div_eq_mul_inv] using add_eq_zero_iff_eq_neg.mp (by linarith [hz])
      exact hm (by linarith [hz'])
    field_simp [hρ0, hm, hs]
    ring
  have hlog :
      Tendsto
        (fun rho : ℝ => Real.log ((r + rho) / (r - rho)))
        atTop (𝓝 (0 : ℝ)) := by
    have h :=
      (Real.continuousAt_log (by norm_num : (-1 : ℝ) ≠ 0)).tendsto.comp hratio
    have hneg : Real.log (-1 : ℝ) = 0 := by
      rw [Real.log_neg_eq_log]
      simp
    simpa [hneg] using h
  have hdiv :
      Tendsto
        (fun rho : ℝ =>
          Real.log ((r + rho) / (r - rho)) / (2 * r))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using hlog.div_const (2 * r)
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop r] with rho hρ
  have hp : r + rho ≠ 0 := by
    have : 0 < r + rho := by linarith
    exact ne_of_gt this
  have hm : r - rho ≠ 0 := by linarith
  unfold pvRationalPrimitive
  rw [Real.log_div hp hm]

/-- For fixed symmetric gap e, sending the outer radius to infinity leaves
only the two-sided singular boundary gap. -/
theorem pvKernel_integral_split_tendsto_gap
    (r e : ℝ) (hr : 0 < r) (he : 0 < e) (her : e < r) :
    Tendsto
      (fun R : ℝ =>
        (∫ x in (0 : ℝ)..(r - e), (r ^ 2 - x ^ 2)⁻¹) +
          (∫ x in (r + e)..R, (r ^ 2 - x ^ 2)⁻¹))
      atTop
      (𝓝 (pvRationalPrimitive r (r - e) -
        pvRationalPrimitive r (r + e))) := by
  have hlim :
      Tendsto
        (fun R : ℝ =>
          (pvRationalPrimitive r (r - e) -
            pvRationalPrimitive r (r + e)) +
            pvRationalPrimitive r R)
        atTop
        (𝓝 (pvRationalPrimitive r (r - e) -
          pvRationalPrimitive r (r + e))) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (pvRationalPrimitive_tendsto_zero_atTop r hr)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (r + e)] with R hR
  exact (pvKernel_integral_split r e R hr he her hR).symm

/-- The remaining gap in the preceding outer-radius limit vanishes as the
symmetric exclusion radius shrinks to zero. -/
theorem pvKernel_gap_tendsto_zero
    (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun e : ℝ =>
        pvRationalPrimitive r (r - e) -
          pvRationalPrimitive r (r + e))
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  symmetricPV_primitive_gap_tendsto_zero r hr

end HBL.Modulation.AffineTail
