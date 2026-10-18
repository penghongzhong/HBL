import HBL.MonopoleRadialLinearization
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Piecewise

/-!
The correct continuous origin value and vanishing radial flux of the
actual cutoff monopole. The source is the existing constructed Fredholm
source, with its already proved continuity and absolute integrability.

These are scalar endpoint statements. A three-dimensional weak equation
still needs its own punctured-domain integration-by-parts theorem.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The natural origin value is the actual Green-source mass, not the
zero imposed by Lean's totalized quotient at the origin. -/
def monopoleRadialOriginValue : ℝ :=
  halfLineGreenTail monopoleRemainderSource 0

/-- Change only the scalar origin value of the actual radial profile. -/
def monopoleInnerRadialContinuous (R : ℝ) : ℝ → ℝ :=
  Function.update (monopoleInnerRadialProfile R) 0 monopoleRadialOriginValue

theorem monopoleInnerProfile_eq_remainder_of_le {R r : ℝ}
    (hR : 0 < R) (hr1 : r ≤ 1) (hrR : r ≤ R) :
    monopoleInnerProfile R r = monopoleRemainder r := by
  unfold monopoleInnerProfile
  rw [cutoff_zero_of_le_one (r / R) ((div_le_one hR).2 hrR)]
  unfold monopoleProfile
  rw [monopoleLogModel_zero_of_le_one r hr1, model_zero_of_le_one r hr1]
  ring

/-- The fixed models and the outer cutoff vanish on an actual neighborhood
of every radius below both cutoff thresholds. -/
theorem monopoleInnerProfile_eq_green_near {R r : ℝ}
    (hR : 0 < R) (hr : r < min 1 R) :
    monopoleInnerProfile R =ᶠ[𝓝 r] halfLineMinGreen monopoleRemainderSource := by
  filter_upwards [Iio_mem_nhds hr] with x hx
  rw [monopoleInnerProfile_eq_remainder_of_le hR
    (le_trans hx.le (min_le_left _ _)) (le_trans hx.le (min_le_right _ _))]
  exact monopoleRemainder_eq_halfLineMinGreen x

/-- The positive-radius quotient tends to the source mass at the origin.
No free source regularity or origin-slope hypothesis is supplied. -/
theorem monopoleInnerRadialProfile_tendsto_origin {R : ℝ} (hR : 0 < R) :
    Tendsto (monopoleInnerRadialProfile R) (𝓝[>] (0 : ℝ))
      (𝓝 monopoleRadialOriginValue) := by
  have hd := halfLineMinGreen_hasDerivWithinAt_zero
    monopoleRemainderSource_continuous monopoleRemainderSource_integrable
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Ici_sdiff_left] at hs
  have hg : Tendsto
      (fun r : ℝ => halfLineMinGreen monopoleRemainderSource r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 monopoleRadialOriginValue) := by
    apply hs.congr'
    filter_upwards with r
    simp only [slope_def_field, halfLineMinGreen_zero, sub_zero]
  have he := monopoleInnerProfile_eq_green_near hR
    (show (0 : ℝ) < min 1 R from lt_min (by norm_num) hR)
  apply hg.congr'
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with r hr
  change halfLineMinGreen monopoleRemainderSource r / r = monopoleInnerProfile R r / r
  rw [hr]

@[simp] theorem monopoleInnerRadialContinuous_zero (R : ℝ) :
    monopoleInnerRadialContinuous R 0 = monopoleRadialOriginValue := by
  simp [monopoleInnerRadialContinuous]

theorem monopoleInnerRadialContinuous_eq {R r : ℝ} (hr : 0 < r) :
    monopoleInnerRadialContinuous R r = monopoleInnerRadialProfile R r := by
  exact Function.update_of_ne hr.ne' _ _

/-- The continuous representative agrees on a neighborhood of each
positive radius, so its derivatives there are the same actual ones. -/
theorem monopoleInnerRadialContinuous_eventuallyEq {R r : ℝ} (hr : 0 < r) :
    monopoleInnerRadialContinuous R =ᶠ[𝓝 r] monopoleInnerRadialProfile R := by
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact monopoleInnerRadialContinuous_eq hx

theorem monopoleInnerRadialContinuous_deriv_eq {R r : ℝ} (hr : 0 < r) :
    deriv (monopoleInnerRadialContinuous R) r =
      deriv (monopoleInnerRadialProfile R) r :=
  (monopoleInnerRadialContinuous_eventuallyEq hr).deriv_eq

/-- The corrected representative is continuous on the closed half-line
and equals the already verified actual profile at every positive radius. -/
theorem monopoleInnerRadialContinuous_continuousOn {R : ℝ} (hR : 0 < R) :
    ContinuousOn (monopoleInnerRadialContinuous R) (Ici (0 : ℝ)) := by
  rw [monopoleInnerRadialContinuous, continuousOn_update_iff, Ici_sdiff_left]
  refine ⟨?_, fun _ => monopoleInnerRadialProfile_tendsto_origin hR⟩
  intro r hr
  exact (monopoleInnerRadialProfile_differentiableAt hr).continuousAt.continuousWithinAt

/-- Exact local flux identity for the same constructed source. The right
side is a finite integral, whose endpoint limit is justified below. -/
theorem monopoleInnerRadialProfile_flux_eq {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hnear : r < min 1 R) :
    r ^ 2 * deriv (monopoleInnerRadialProfile R) r =
      -(∫ rho in (0 : ℝ)..r, rho * monopoleRemainderSource rho) := by
  have he := monopoleInnerProfile_eq_green_near hR hnear
  have hq := he.eq_of_nhds
  have hd : deriv (monopoleInnerProfile R) r =
      halfLineGreenTail monopoleRemainderSource r := by
    rw [he.deriv_eq]
    exact (halfLineMinGreen_hasDerivAt monopoleRemainderSource_continuous
      monopoleRemainderSource_integrable hr).deriv
  have hquot := div_radius_hasDerivAt (monopoleInnerProfile R) hr
    (monopoleInnerProfile_differentiableAt hr)
  calc
    r ^ 2 * deriv (monopoleInnerRadialProfile R) r =
        r * deriv (monopoleInnerProfile R) r - monopoleInnerProfile R r := by
      change r ^ 2 * deriv (fun x => monopoleInnerProfile R x / x) r = _
      rw [hquot.deriv]
      field_simp [hr.ne']
    _ = _ := by
      rw [hd, hq, halfLineMinGreen_split monopoleRemainderSource_continuous
        monopoleRemainderSource_integrable hr]
      ring

/-- The scalar boundary flux vanishes at the origin. This does not by
itself claim the as-yet-separate three-dimensional weak equation. -/
theorem monopoleInnerRadialProfile_flux_tendsto_zero {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => r ^ 2 * deriv (monopoleInnerRadialProfile R) r)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hc : Continuous (fun r : ℝ =>
      ∫ rho in (0 : ℝ)..r, rho * monopoleRemainderSource rho) :=
    intervalIntegral.continuous_primitive
      (fun a b => (continuous_id.mul monopoleRemainderSource_continuous).intervalIntegrable a b) 0
  have hz : Tendsto (fun r : ℝ =>
      -(∫ rho in (0 : ℝ)..r, rho * monopoleRemainderSource rho))
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [intervalIntegral.integral_same, neg_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.neg
  apply (hz.mono_left nhdsWithin_le_nhds).congr'
  have hmin : (0 : ℝ) < min 1 R := lt_min (by norm_num) hR
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hmin)] with r hr hnear
  exact (monopoleInnerRadialProfile_flux_eq hR hr hnear).symm

/-- The zero-flux endpoint statement also holds for the continuous
representative itself, rather than only the totalized radial quotient. -/
theorem monopoleInnerRadialContinuous_flux_tendsto_zero {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => r ^ 2 * deriv (monopoleInnerRadialContinuous R) r)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply (monopoleInnerRadialProfile_flux_tendsto_zero hR).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [monopoleInnerRadialContinuous_deriv_eq hr]

/-- The actual amplitude-dependent radius automatically satisfies every
radius hypothesis in the continuous-origin and zero-flux conclusions. -/
theorem monopoleQuadraticRadius_origin_control {c : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) :
    ContinuousOn (monopoleInnerRadialContinuous (monopoleQuadraticRadius c)) (Ici (0 : ℝ)) ∧
      Tendsto (fun r : ℝ => r ^ 2 *
        deriv (monopoleInnerRadialContinuous (monopoleQuadraticRadius c)) r)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hR : 0 < monopoleQuadraticRadius c :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (monopoleQuadraticRadius_ge_four hc hc1)
  exact ⟨monopoleInnerRadialContinuous_continuousOn hR,
    monopoleInnerRadialContinuous_flux_tendsto_zero hR⟩

end HBL.Modulation.Monopole
