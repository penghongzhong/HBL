import HBL.MonopoleMovingCutoffDerivative

/-! Time differentiation of the actual amplitude-dependent cutoff profile.
The amplitude may cross zero. All statements concern a fixed spatial radius
and an actual differentiable scalar path; no radiation dynamics or outer
matching equation is assumed or constructed here. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- At zero amplitude the cutoff is constant on an amplitude neighborhood
of every fixed radius. Thus the actual profile has derivative equal to the
radial monopole, even though the absolute value is not differentiable at zero. -/
theorem monopoleMovingCutoffProfile_zero_hasDerivAt (r : ℝ) :
    HasDerivAt (fun a => monopolePerturbedRadialProfile (monopoleQuadraticRadius a) a r)
      (monopoleRadialProfile r) 0 := by
  have harg : ContinuousAt (fun a : ℝ => |a| * r / 4) 0 := by fun_prop
  have hz : |(0 : ℝ)| * r / 4 < 1 := by norm_num
  have hev := harg.eventually (Iio_mem_nhds hz)
  have hmodel : HasDerivAt (fun a : ℝ => bubble r + a * monopoleRadialProfile r)
      (monopoleRadialProfile r) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (bubble r)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (monopoleRadialProfile r)) using 1
    · rfl
    · simp
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [hev] with a ha
  change |a| * r / 4 < 1 at ha
  rw [monopoleMovingCutoffProfile_eq, cutoff_zero_of_le_one _ ha.le]
  ring

/-- The global amplitude derivative, including zero amplitude, retains
the annular contribution from differentiating the moving cutoff. -/
theorem monopoleMovingCutoffProfile_hasDerivAt_all (c r : ℝ) :
    HasDerivAt (fun a => monopolePerturbedRadialProfile (monopoleQuadraticRadius a) a r)
      (monopoleRadialProfile r *
        (1 - cutoff (|c| * r / 4) - (|c| * r / 4) * deriv cutoff (|c| * r / 4))) c := by
  by_cases hc : c = 0
  · subst c
    simpa only [abs_zero, zero_mul, zero_div,
      cutoff_zero_of_le_one (0 : ℝ) (by norm_num), sub_zero, mul_one] using
      monopoleMovingCutoffProfile_zero_hasDerivAt r
  · exact monopoleMovingCutoffProfile_hasDerivAt hc r

/-- The scalar chain rule for the actual moving-cutoff path at a fixed
radius. The input is differentiability of the amplitude, not a radiation law. -/
theorem monopoleMovingCutoffTime_hasDerivAt {c : ℝ → ℝ} {cs s : ℝ}
    (hc : HasDerivAt c cs s) (r : ℝ) :
    HasDerivAt
      (fun t => monopolePerturbedRadialProfile (monopoleQuadraticRadius (c t)) (c t) r)
      (cs * monopoleRadialProfile r *
        (1 - cutoff (|c s| * r / 4) - (|c s| * r / 4) * deriv cutoff (|c s| * r / 4)))
      s := by
  convert (monopoleMovingCutoffProfile_hasDerivAt_all (c s) r).comp s hc using 1
  · rfl
  · ring

/-- The core time derivative is the amplitude velocity times the actual
radial monopole. The strict cutoff condition also permits zero amplitude. -/
theorem monopoleMovingCutoffTime_core_hasDerivAt {c : ℝ → ℝ} {cs s r : ℝ}
    (hc : HasDerivAt c cs s) (hcore : |c s| * r / 4 < 1) :
    HasDerivAt
      (fun t => monopolePerturbedRadialProfile (monopoleQuadraticRadius (c t)) (c t) r)
      (cs * monopoleRadialProfile r) s := by
  simpa only [cutoff_zero_of_le_one _ hcore.le, cutoff_deriv_zero_of_lt_one hcore,
    mul_zero, sub_zero, mul_one] using monopoleMovingCutoffTime_hasDerivAt hc r

/-- The actual core time derivative has a bound uniform over all positive
radii and all amplitudes, including a zero crossing, in terms of the scalar
amplitude velocity and the already constructed radial monopole bound. -/
theorem monopoleMovingCutoffTime_core_deriv_abs_le {c : ℝ → ℝ} {cs s r : ℝ}
    (hc : HasDerivAt c cs s) (hr : 0 < r) (hcore : |c s| * r / 4 < 1) :
    |deriv
      (fun t => monopolePerturbedRadialProfile (monopoleQuadraticRadius (c t)) (c t) r) s| ≤
      monopoleRadialBoundConstant * |cs| := by
  rw [(monopoleMovingCutoffTime_core_hasDerivAt hc hcore).deriv, abs_mul,
    mul_comm monopoleRadialBoundConstant]
  exact mul_le_mul_of_nonneg_left (monopoleRadialProfile_abs_le hr) (abs_nonneg cs)

end HBL.Modulation.Monopole
