import HBL.MonopoleStaticRadialBound

/-! Parameter differentiation of the actual amplitude-dependent cutoff path.
The cutoff radius is varied with the amplitude; the annular derivative is
retained globally and disappears only on the strict interior of the core. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- Rewriting the actual radius-dependent profile, including its cutoff,
as one function of the amplitude. -/
theorem monopoleMovingCutoffProfile_eq (c r : ℝ) :
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r =
      bubble r + c * (1 - cutoff (|c| * r / 4)) * monopoleRadialProfile r := by
  have harg : r / monopoleQuadraticRadius c = |c| * r / 4 := by
    unfold monopoleQuadraticRadius
    rw [div_div_eq_mul_div]
    ring
  unfold monopolePerturbedRadialProfile monopoleInnerRadialProfile monopoleInnerProfile
    monopoleRadialProfile
  rw [harg]
  ring

/-- The global derivative along the actual moving-cutoff path, with the
additional annular cutoff derivative retained. No spatial derivative is taken. -/
theorem monopoleMovingCutoffProfile_hasDerivAt {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    HasDerivAt (fun a => monopolePerturbedRadialProfile (monopoleQuadraticRadius a) a r)
      (monopoleRadialProfile r *
        (1 - cutoff (|c| * r / 4) - (|c| * r / 4) * deriv cutoff (|c| * r / 4))) c := by
  have habs : HasDerivAt (fun a : ℝ => |a|) (|c| / c) c := by
    rcases hc.lt_or_gt with hn | hp
    · have hneg : HasDerivAt (fun a : ℝ => |a|) (-1) c := by
        apply (hasDerivAt_neg c).congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hn] with a ha
        exact abs_of_neg ha
      convert hneg using 1
      rw [abs_of_neg hn]
      field_simp [hc]
    · have hpos : HasDerivAt (fun a : ℝ => |a|) 1 c := by
        apply (hasDerivAt_id c).congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hp] with a ha
        exact abs_of_pos ha
      convert hpos using 1
      rw [abs_of_pos hp, div_self hc]
  have harg := (habs.mul_const r).div_const 4
  have hcut := ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1
    (|c| * r / 4)).hasDerivAt.comp c harg
  have hmodel := (hasDerivAt_const c (bubble r)).add
    (((hasDerivAt_id c).mul ((hasDerivAt_const c (1 : ℝ)).sub hcut)).mul_const
      (monopoleRadialProfile r))
  convert hmodel using 1
  · funext a
    exact monopoleMovingCutoffProfile_eq a r
  · simp only [id_eq, zero_add, one_mul, zero_sub, Pi.sub_apply, Function.comp_apply]
    field_simp [hc]
    ring

/-- On the strict interior where the cutoff is identically zero, so is its
actual derivative. This is a neighborhood statement, not a formal substitution. -/
theorem cutoff_deriv_zero_of_lt_one {z : ℝ} (hz : z < 1) :
    deriv cutoff z = 0 := by
  have he : cutoff =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hz] with x hx
    exact cutoff_zero_of_le_one x (le_of_lt hx)
  rw [he.deriv_eq]
  exact deriv_const z 0

/-- The fixed-spatial-radius derivative of the actual moving path is the
bare radial monopole on the core, whose cutoff argument is at most one half. -/
theorem monopoleMovingCutoffProfile_core_hasDerivAt {c r : ℝ}
    (hc : 0 < |c|) (hsep : r ≤ monopoleQuadraticRadius c / 2) :
    HasDerivAt (fun a => monopolePerturbedRadialProfile (monopoleQuadraticRadius a) a r)
      (monopoleRadialProfile r) c := by
  have hc0 : c ≠ 0 := by exact fun h => by simpa [h] using hc
  have hz : |c| * r / 4 ≤ 1 / 2 := by
    unfold monopoleQuadraticRadius at hsep
    have h := mul_le_mul_of_nonneg_left hsep hc.le
    field_simp [hc.ne'] at h ⊢
    nlinarith
  have hz1 : |c| * r / 4 < 1 := by linarith
  simpa only [cutoff_zero_of_le_one _ hz1.le, cutoff_deriv_zero_of_lt_one hz1,
    mul_zero, sub_zero, mul_one] using monopoleMovingCutoffProfile_hasDerivAt hc0 r

end HBL.Modulation.Monopole
