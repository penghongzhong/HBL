import HBL.AffineTailLogGlobalIntegrability

/-!
Unconditional evaluation of the absolutely convergent affine logarithmic
integral.  We pass to infinity along one explicit joint cutoff path, while
the preceding module guarantees that this path recovers the Lebesgue
integral.  Every finite-cutoff identity is an ordinary interval identity.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.AffineTail

/-- Logarithmic boundary contribution at the symmetric gap. -/
def affineLogSingularBoundary (r e : ℝ) : ℝ :=
  (Real.log (r + (r - e)) - Real.log (r - (r - e))) *
      radialLogPrimitive (r - e) -
    (Real.log (r + (r + e)) - Real.log (r - (r + e))) *
      radialLogPrimitive (r + e)

/-- Logarithmic boundary contribution at the finite outer endpoint. -/
def affineLogFarBoundary (r R : ℝ) : ℝ :=
  (Real.log (r + R) - Real.log (r - R)) * radialLogPrimitive R

/-- The explicit weighted primitive evaluates the derivative term on every
finite interval avoiding the two poles. -/
theorem affinePVWeightedPrimitive_integral_away
    (r a b : ℝ) (hr : r ≠ 0)
    (havoid : ∀ x ∈ Set.uIcc a b, r + x ≠ 0 ∧ r - x ≠ 0) :
    (∫ x in a..b,
      (2 * r / (r ^ 2 - x ^ 2)) * radialLogPrimitive x) =
      affinePVWeightedPrimitive r b - affinePVWeightedPrimitive r a := by
  have hden : ∀ x ∈ Set.uIcc a b, r ^ 2 - x ^ 2 ≠ 0 := by
    intro x hx hz
    have hprod : (r + x) * (r - x) = 0 := by nlinarith [hz]
    exact (mul_ne_zero (havoid x hx).1 (havoid x hx).2) hprod
  have hfirst : ContinuousOn
      (fun x : ℝ => 2 * r / (r ^ 2 - x ^ 2)) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const
      (continuous_const.sub (continuous_id.pow 2)).continuousOn
    exact hden
  have hprimitive : Continuous radialLogPrimitive := by
    unfold radialLogPrimitive
    fun_prop (discharger := intro; positivity)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => affinePVWeightedPrimitive_hasDerivAt r x hr
      (havoid x hx).1 (havoid x hx).2)
    (hfirst.mul hprimitive.continuousOn).intervalIntegrable

/-- Exact primitive formula for the two finite pieces around the pole. -/
theorem affinePVWeightedPrimitive_integral_split
    (r e R : ℝ) (hr : 0 < r) (he : 0 < e)
    (her : e < r) (hR : r + e ≤ R) :
    (∫ x in (0 : ℝ)..(r - e),
        (2 * r / (r ^ 2 - x ^ 2)) * radialLogPrimitive x) +
      (∫ x in (r + e)..R,
        (2 * r / (r ^ 2 - x ^ 2)) * radialLogPrimitive x) =
      affinePVWeightedPrimitive r R +
        (affinePVWeightedPrimitive r (r - e) -
          affinePVWeightedPrimitive r (r + e)) := by
  have h0 : (0 : ℝ) ≤ r - e := by linarith
  have hleft : ∀ x ∈ Set.uIcc (0 : ℝ) (r - e),
      r + x ≠ 0 ∧ r - x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    exact ⟨ne_of_gt (by linarith [hx.1]), ne_of_gt (by linarith [hx.2])⟩
  have hright : ∀ x ∈ Set.uIcc (r + e) R,
      r + x ≠ 0 ∧ r - x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hR] at hx
    exact ⟨ne_of_gt (by linarith [hx.1]), ne_of_lt (by linarith [hx.1])⟩
  rw [affinePVWeightedPrimitive_integral_away r 0 (r - e)
      (ne_of_gt hr) hleft,
    affinePVWeightedPrimitive_integral_away r (r + e) R
      (ne_of_gt hr) hright,
    affinePVWeightedPrimitive_zero]
  ring

/-- The symmetric logarithmic boundary jump vanishes. -/
theorem affineLogSingularBoundary_tendsto_zero
    (r : ℝ) (hr : 0 < r) :
    Tendsto (affineLogSingularBoundary r) (𝓝 0) (𝓝 0) := by
  have hminus : Tendsto (fun e : ℝ => r - e) (𝓝 0) (𝓝 r) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_id : Tendsto (fun e : ℝ => e) (𝓝 0) (𝓝 0))
  have hplus : Tendsto (fun e : ℝ => r + e) (𝓝 0) (𝓝 r) := by
    simpa using tendsto_const_nhds.add
      (tendsto_id : Tendsto (fun e : ℝ => e) (𝓝 0) (𝓝 0))
  have hPminus : Tendsto (fun e : ℝ => radialLogPrimitive (r - e))
      (𝓝 0) (𝓝 (radialLogPrimitive r)) := by
    simpa only [Function.comp_def] using
      (radialLogPrimitive_hasDerivAt r).continuousAt.tendsto.comp hminus
  have hPplus : Tendsto (fun e : ℝ => radialLogPrimitive (r + e))
      (𝓝 0) (𝓝 (radialLogPrimitive r)) := by
    simpa only [Function.comp_def] using
      (radialLogPrimitive_hasDerivAt r).continuousAt.tendsto.comp hplus
  have hlogMinus : Tendsto (fun e : ℝ => Real.log (2 * r - e))
      (𝓝 0) (𝓝 (Real.log (2 * r))) := by
    have harg : Tendsto (fun e : ℝ => 2 * r - e)
        (𝓝 0) (𝓝 (2 * r)) := by
      simpa using tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun e : ℝ => e) (𝓝 0) (𝓝 0))
    exact (Real.continuousAt_log (ne_of_gt (by positivity : (0 : ℝ) < 2 * r))).tendsto.comp harg
  have hlogPlus : Tendsto (fun e : ℝ => Real.log (2 * r + e))
      (𝓝 0) (𝓝 (Real.log (2 * r))) := by
    have harg : Tendsto (fun e : ℝ => 2 * r + e)
        (𝓝 0) (𝓝 (2 * r)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_id : Tendsto (fun e : ℝ => e) (𝓝 0) (𝓝 0))
    exact (Real.continuousAt_log (ne_of_gt (by positivity : (0 : ℝ) < 2 * r))).tendsto.comp harg
  have hregular := (hPminus.mul hlogMinus).sub (hPplus.mul hlogPlus)
  have hregular0 : Tendsto
      (fun e : ℝ =>
        radialLogPrimitive (r - e) * Real.log (2 * r - e) -
          radialLogPrimitive (r + e) * Real.log (2 * r + e))
      (𝓝 0) (𝓝 0) := by
    simpa only [sub_self] using hregular
  have htotal := hregular0.sub (radialLogPrimitive_log_gap_tendsto_zero r)
  have htotal0 : Tendsto
      (fun e : ℝ =>
        radialLogPrimitive (r - e) * Real.log (2 * r - e) -
          radialLogPrimitive (r + e) * Real.log (2 * r + e) -
          (radialLogPrimitive (r - e) - radialLogPrimitive (r + e)) *
            Real.log e)
      (𝓝 0) (𝓝 0) := by simpa using htotal
  apply htotal0.congr'
  filter_upwards with e
  unfold affineLogSingularBoundary
  rw [show r + (r - e) = 2 * r - e by ring,
    show r - (r - e) = e by ring,
    show r + (r + e) = 2 * r + e by ring,
    show r - (r + e) = -e by ring,
    Real.log_neg_eq_log]
  ring

/-- The rational primitive multiplying the outer logarithm vanishes. -/
theorem radialLogPrimitive_tendsto_zero_atTop :
    Tendsto radialLogPrimitive atTop (𝓝 0) := by
  have h := rational_over_one_add_sq_tendsto_zero.pow 2 |>.div_const 4
  norm_num at h
  apply h.congr'
  filter_upwards with x
  unfold radialLogPrimitive
  field_simp [(by positivity : (1 + x ^ 2 : ℝ) ≠ 0)]

/-- The complete logarithmic outer boundary vanishes. -/
theorem affineLogFarBoundary_tendsto_zero
    (r : ℝ) (hr : 0 < r) :
    Tendsto (affineLogFarBoundary r) atTop (𝓝 0) := by
  have hlog0 := (pvRationalPrimitive_tendsto_zero_atTop r hr).const_mul (2 * r)
  have hlog : Tendsto
      (fun R : ℝ => Real.log (r + R) - Real.log (r - R))
      atTop (𝓝 0) := by
    convert hlog0 using 1
    · funext R
      unfold pvRationalPrimitive
      field_simp [ne_of_gt hr]
    · simp
  have hmul := hlog.mul radialLogPrimitive_tendsto_zero_atTop
  change Tendsto
    (fun R : ℝ =>
      (Real.log (r + R) - Real.log (r - R)) * radialLogPrimitive R)
    atTop (𝓝 0)
  simpa only [zero_mul] using hmul

/-- The finite integration-by-parts formula rewritten entirely in terms of
the three explicit boundary contributions. -/
theorem affineLogDensity_cutoff_eq_boundary
    (r e R : ℝ) (hr : 0 < r) (he : 0 < e)
    (her : e < r) (hR : r + e ≤ R) :
    (∫ x in (0 : ℝ)..(r - e), affineLogDensity r x) +
        (∫ x in (r + e)..R, affineLogDensity r x) =
      affineLogSingularBoundary r e + affineLogFarBoundary r R -
        (affinePVWeightedPrimitive r R +
          (affinePVWeightedPrimitive r (r - e) -
            affinePVWeightedPrimitive r (r + e))) := by
  rw [affineLogDensity_integral_split_ibp r e R hr he her hR,
    affinePVWeightedPrimitive_integral_split r e R hr he her hR]
  unfold affineLogSingularBoundary affineLogFarBoundary
  simp [radialLogPrimitive]
  ring

/-- The affine logarithmic integral has the exact value required by the
real-channel zero-mode identity. -/
theorem affineLogIntegral_eq_expected (r : ℝ) (hr : 0 < r) :
    affineLogIntegral r = affineLogIntegralExpected r := by
  let e : ℝ → ℝ := fun R => r * R⁻¹
  have he0 : Tendsto e atTop (𝓝 0) := by
    simpa only [e, mul_zero] using tendsto_inv_atTop_zero.const_mul r
  have hcut : Tendsto
      (fun R : ℝ =>
        (∫ x in (0 : ℝ)..(r - e R), affineLogDensity r x) +
          (∫ x in (r + e R)..R, affineLogDensity r x))
      atTop (𝓝 (affineLogIntegral r)) := by
    simpa only [id_eq] using
      affineLogDensity_cutoff_tendsto atTop r hr id e tendsto_id he0
  have hnear := (affineLogSingularBoundary_tendsto_zero r hr).comp he0
  have hfar := affineLogFarBoundary_tendsto_zero r hr
  have hweighted : Tendsto
      (fun R : ℝ =>
        affinePVWeightedPrimitive r R +
          (affinePVWeightedPrimitive r (r - e R) -
            affinePVWeightedPrimitive r (r + e R)))
      atTop
      (𝓝 (Real.pi * r * (r ^ 2 - 1) /
        (8 * (1 + r ^ 2) ^ 2))) := by
    have hgap := (affinePVWeightedPrimitive_gap_tendsto_zero r hr).comp he0
    have h := (affinePVWeightedPrimitive_tendsto_atTop r hr).add hgap
    simpa only [Function.comp_def, add_zero] using h
  have hrhs : Tendsto
      (fun R : ℝ =>
        affineLogSingularBoundary r (e R) + affineLogFarBoundary r R -
          (affinePVWeightedPrimitive r R +
            (affinePVWeightedPrimitive r (r - e R) -
              affinePVWeightedPrimitive r (r + e R))))
      atTop
      (𝓝 (-(Real.pi * r * (r ^ 2 - 1) /
        (8 * (1 + r ^ 2) ^ 2)))) := by
    have h := (hnear.add hfar).sub hweighted
    simpa only [Function.comp_def, zero_add, zero_sub] using h
  have hcutValue : Tendsto
      (fun R : ℝ =>
        (∫ x in (0 : ℝ)..(r - e R), affineLogDensity r x) +
          (∫ x in (r + e R)..R, affineLogDensity r x))
      atTop
      (𝓝 (-(Real.pi * r * (r ^ 2 - 1) /
        (8 * (1 + r ^ 2) ^ 2)))) := by
    apply hrhs.congr'
    filter_upwards [eventually_gt_atTop (max 1 (2 * r))] with R hRlarge
    have hRone : 1 < R :=
      lt_of_le_of_lt (le_max_left (1 : ℝ) (2 * r)) hRlarge
    have hRtwo : 2 * r < R :=
      lt_of_le_of_lt (le_max_right (1 : ℝ) (2 * r)) hRlarge
    have hRpos : 0 < R := lt_trans (by norm_num) hRone
    have hinvpos : 0 < R⁻¹ := inv_pos.mpr hRpos
    have hinvlt : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hRone
    have hepos : 0 < e R := by
      dsimp [e]
      exact mul_pos hr hinvpos
    have her : e R < r := by
      dsimp [e]
      simpa using mul_lt_mul_of_pos_left hinvlt hr
    have houter : r + e R ≤ R := by linarith
    exact (affineLogDensity_cutoff_eq_boundary
      r (e R) R hr hepos her houter).symm
  have hvalue :
      affineLogIntegral r =
        -(Real.pi * r * (r ^ 2 - 1) /
          (8 * (1 + r ^ 2) ^ 2)) :=
    tendsto_nhds_unique hcut hcutValue
  rw [hvalue]
  unfold affineLogIntegralExpected
  ring

/-- The real-channel scaling resonance is now an unconditional zero mode. -/
theorem hPlus_resonancePlus_zero :
    ∀ r : ℝ, 0 < r → hPlusApply resonancePlus r = 0 := by
  apply hPlus_zero_of_affineLogIntegral_expected
  exact affineLogIntegral_eq_expected

end HBL.Modulation.AffineTail
