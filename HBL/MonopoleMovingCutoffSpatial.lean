import HBL.MonopoleMovingCutoffTime

/-!
Spatial differentiation and dilation of the same globally truncated monopole.
The global identity retains the annular derivative of the actual cutoff. All
statements concern positive scalar radii; no three-dimensional lift is asserted.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- Spatial derivative of the actual profile, for every amplitude including
zero. The cutoff radius is held at its actual value for that amplitude. -/
theorem monopoleMovingCutoffSpatial_hasDerivAt (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
      (deriv bubble r + c * ((1 - cutoff (|c| * r / 4)) *
        deriv monopoleRadialProfile r - (|c| / 4) *
          deriv cutoff (|c| * r / 4) * monopoleRadialProfile r)) r := by
  have harg : HasDerivAt (fun x : ℝ => |c| * x / 4) (|c| / 4) r := by
    convert ((hasDerivAt_id r).const_mul |c|).div_const 4 using 1 <;> simp
  have hcut := ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1
    (|c| * r / 4)).hasDerivAt.comp r harg
  have hprofile := (monopoleRadialProfile_hasDerivAt hr).differentiableAt.hasDerivAt
  have hmodel := (bubble_differentiable r).hasDerivAt.add
    ((((hasDerivAt_const r (1 : ℝ)).sub hcut).mul hprofile).const_mul c)
  convert hmodel using 1
  · funext x
    rw [monopoleMovingCutoffProfile_eq]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  · simp only [Pi.sub_apply, Function.comp_apply]
    ring

/-- On the strict core the spatial derivative is the true derivative of
the bubble plus the actual monopole, without a cutoff term. -/
theorem monopoleMovingCutoffSpatial_core_hasDerivAt (c : ℝ) {r : ℝ}
    (hr : 0 < r) (hcore : |c| * r / 4 < 1) :
    HasDerivAt (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
      (deriv bubble r + c * deriv monopoleRadialProfile r) r := by
  simpa only [cutoff_zero_of_le_one _ hcore.le, cutoff_deriv_zero_of_lt_one hcore,
    sub_zero, one_mul, mul_zero, zero_mul] using monopoleMovingCutoffSpatial_hasDerivAt c hr

/-- Exact dilation increment of the globally truncated profile. In the
transition annulus the derivative of the cutoff remains in the formula. -/
theorem monopoleMovingCutoff_dilation_eq (c : ℝ) {r : ℝ} (hr : 0 < r) :
    dilationGenerator (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) r -
        dilationGenerator bubble r =
      c * ((1 - cutoff (|c| * r / 4)) * dilationGenerator monopoleRadialProfile r -
        (|c| * r / 4) * deriv cutoff (|c| * r / 4) * monopoleRadialProfile r) := by
  unfold dilationGenerator
  rw [(monopoleMovingCutoffSpatial_hasDerivAt c hr).deriv,
    monopoleMovingCutoffProfile_eq]
  ring

/-- The actual core dilation increment is exactly the amplitude times
the dilation of the already constructed radial monopole. -/
theorem monopoleMovingCutoff_dilation_core_eq (c : ℝ) {r : ℝ}
    (hr : 0 < r) (hcore : |c| * r / 4 < 1) :
    dilationGenerator (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) r -
        dilationGenerator bubble r = c * dilationGenerator monopoleRadialProfile r := by
  simpa only [cutoff_zero_of_le_one _ hcore.le, cutoff_deriv_zero_of_lt_one hcore,
    sub_zero, one_mul, mul_zero, zero_mul] using monopoleMovingCutoff_dilation_eq c hr

/-- Quotient conjugation expresses the actual monopole dilation through
the fixed smooth models and the integrable Fredholm source. -/
theorem monopoleRadialProfile_dilation_green_eq {r : ℝ} (hr : 0 < r) :
    dilationGenerator monopoleRadialProfile r =
      deriv monopoleLogModel r + monopoleAffineSlope * deriv model r +
        halfLineGreenTail monopoleRemainderSource r - monopoleRadialProfile r / 2 := by
  unfold dilationGenerator
  rw [(monopoleRadialProfile_hasDerivAt hr).deriv]
  unfold monopoleRadialProfile
  field_simp [hr.ne']
  ring

private theorem monopoleFixedModel_derivative_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      |deriv monopoleLogModel r + monopoleAffineSlope * deriv model r| ≤ C := by
  have hlog : Continuous (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp monopoleLogModel_contDiff_infty).2.continuous
  have hmodel : Continuous (deriv model) :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).2.continuous
  rcases isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 3) (hlog.add (hmodel.const_mul monopoleAffineSlope)).continuousOn
    with ⟨B, hB⟩
  refine ⟨|B| + 1 + |monopoleAffineSlope|, by positivity, ?_⟩
  intro r hr
  by_cases hr3 : r ≤ 3
  · have hb := hB r ⟨hr.le, hr3⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by linarith [le_abs_self B, abs_nonneg monopoleAffineSlope])
  · have hrtwo : 2 < r := by linarith
    rw [monopoleLogModel_deriv_eq_inv_of_two_lt r hrtwo,
      model_deriv_eq_one_of_two_lt r hrtwo, mul_one]
    have hinv : |r⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr hr)]
      exact (inv_le_one₀ hr).mpr (by linarith)
    exact (abs_add_le _ _).trans (by linarith [abs_nonneg B])

/-- A genuine finite bound for the dilation of the constructed monopole
on the entire positive half-line. Its inputs are proved source integrability,
the fixed models, and the previously proved bound on the actual profile. -/
theorem monopoleRadialProfile_dilation_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      |dilationGenerator monopoleRadialProfile r| ≤ C := by
  obtain ⟨B, hBpos, hB⟩ := monopoleFixedModel_derivative_bounded
  let M : ℝ := ∫ rho in Ioi (0 : ℝ), |monopoleRemainderSource rho|
  have hM : 0 ≤ M := integral_nonneg (fun _ => abs_nonneg _)
  refine ⟨B + M + monopoleRadialBoundConstant / 2, by
    have := monopoleRadialBoundConstant_pos
    positivity, ?_⟩
  intro r hr
  have htail : |halfLineGreenTail monopoleRemainderSource r| ≤ M := by
    unfold halfLineGreenTail
    calc
      |∫ rho in Ioi r, monopoleRemainderSource rho| ≤
          ∫ rho in Ioi r, |monopoleRemainderSource rho| := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm monopoleRemainderSource
            (μ := volume.restrict (Ioi r)))
      _ ≤ M := setIntegral_mono_set monopoleRemainderSource_integrable.abs
        (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (Ioi_subset_Ioi hr.le).eventuallySubset
  rw [monopoleRadialProfile_dilation_green_eq hr]
  calc
    |deriv monopoleLogModel r + monopoleAffineSlope * deriv model r +
        halfLineGreenTail monopoleRemainderSource r - monopoleRadialProfile r / 2| ≤
      |deriv monopoleLogModel r + monopoleAffineSlope * deriv model r| +
        |halfLineGreenTail monopoleRemainderSource r| + |monopoleRadialProfile r / 2| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le (deriv monopoleLogModel r + monopoleAffineSlope * deriv model r +
        halfLineGreenTail monopoleRemainderSource r) (-(monopoleRadialProfile r / 2))).trans (by
        rw [abs_neg]
        exact add_le_add
          (abs_add_le (deriv monopoleLogModel r + monopoleAffineSlope * deriv model r)
            (halfLineGreenTail monopoleRemainderSource r)) le_rfl)
    _ ≤ B + M + monopoleRadialBoundConstant / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (add_le_add (hB r hr) htail)
        (div_le_div_of_nonneg_right (monopoleRadialProfile_abs_le hr) (by norm_num))

/-- The actual dilation increment is uniformly linear in amplitude on
every positive core radius, including at a zero amplitude. -/
theorem monopoleMovingCutoff_dilation_core_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ c r : ℝ, 0 < r → |c| * r / 4 < 1 →
      |dilationGenerator (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) r -
        dilationGenerator bubble r| ≤ C * |c| := by
  obtain ⟨C, hCpos, hC⟩ := monopoleRadialProfile_dilation_bounded
  refine ⟨C, hCpos, ?_⟩
  intro c r hr hcore
  rw [monopoleMovingCutoff_dilation_core_eq c hr hcore, abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC r hr) (abs_nonneg c)

end HBL.Modulation.Monopole
