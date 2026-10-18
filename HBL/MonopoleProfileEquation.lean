import HBL.MonopoleProfileTail
import HBL.MonopoleFredholmRegularity

/-!
The classical equation of the actual monopole profile.  Integral linearity
is justified by the square-integrable kernel rows and the actual weighted
data; derivative linearity is justified by pointwise derivative proofs.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The source in the conjugated first monopole equation. -/
def monopoleSource (r : ℝ) : ℝ := r * bubble r ^ 3

theorem nonlocalApply_integrable_of_weighted_memLp
    (q : ℝ → ℝ)
    (hq : MemLp (fun rho => weightedGreenDecay rho * q rho) 2 halfLineMeasure)
    {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun rho : ℝ => hartreeKernel r rho * q rho)
      halfLineMeasure := by
  have hrow := (weightedHartreeKernel_row_memLp hr).integrable_mul hq
  have hscaled := hrow.const_mul (weightedGreenDecay r)
  refine hscaled.congr ?_
  filter_upwards with rho
  have hw (x : ℝ) : weightedGreenDecay x = bubble x ^ 2 := by
    simp only [weightedGreenDecay, bubble_sq]
  change weightedGreenDecay r *
      (weightedHartreeKernel r rho * (weightedGreenDecay rho * q rho)) =
    hartreeKernel r rho * q rho
  rw [hw r, hw rho]
  unfold weightedHartreeKernel hartreeKernel hartreeRadialLog
  ring

theorem nonlocalApply_monopoleProfile
    {r : ℝ} (hr : 0 ≤ r) :
    nonlocalApply monopoleProfile r =
      nonlocalApply monopoleLogModel r +
        monopoleAffineSlope * nonlocalApply model r +
          nonlocalApply monopoleRemainder r := by
  have hlog := nonlocalApply_integrable_of_weighted_memLp
    monopoleLogModel weightedLogModel_memLp_two hr
  have haff := nonlocalApply_integrable_of_weighted_memLp
    model weightedAffineModel_memLp_two hr
  have hrem := nonlocalApply_integrable_of_weighted_memLp
    monopoleRemainder monopoleRemainder_weighted_memLp_two hr
  unfold nonlocalApply
  have heq : (fun rho : ℝ => hartreeKernel r rho * monopoleProfile rho) =
      fun rho =>
        (hartreeKernel r rho * monopoleLogModel rho +
          monopoleAffineSlope * (hartreeKernel r rho * model rho)) +
            hartreeKernel r rho * monopoleRemainder rho := by
    funext rho
    unfold monopoleProfile
    ring
  have htotal := integral_add (hlog.add (haff.const_mul monopoleAffineSlope)) hrem
  have hmiddle := integral_add hlog (haff.const_mul monopoleAffineSlope)
  simp only [Pi.add_apply, halfLineMeasure] at htotal hmiddle
  rw [heq, htotal, hmiddle, integral_const_mul]

theorem monopoleProfile_continuous : Continuous monopoleProfile := by
  exact (monopoleLogModel_contDiff_infty.continuous.add
    (model_contDiff_infty.continuous.const_mul monopoleAffineSlope)).add
      monopoleRemainder_continuous

theorem monopoleProfile_hasDerivAt
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt monopoleProfile
      (deriv monopoleLogModel r + monopoleAffineSlope * deriv model r +
        halfLineGreenTail monopoleRemainderSource r) r := by
  have hlog := ((contDiff_infty_iff_deriv.mp
    monopoleLogModel_contDiff_infty).1 r).hasDerivAt
  have haff := ((contDiff_infty_iff_deriv.mp
    model_contDiff_infty).1 r).hasDerivAt
  exact (hlog.add (haff.const_mul monopoleAffineSlope)).add
    (monopoleRemainder_hasDerivAt hr)

theorem monopoleProfile_second_hasDerivAt
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv monopoleProfile)
      (deriv (deriv monopoleLogModel) r +
        monopoleAffineSlope * deriv (deriv model) r -
          monopoleRemainderSource r) r := by
  have hlog1 : ContDiff ℝ ∞ (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp monopoleLogModel_contDiff_infty).2
  have haff1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).2
  have hlog := ((contDiff_infty_iff_deriv.mp hlog1).1 r).hasDerivAt
  have haff := ((contDiff_infty_iff_deriv.mp haff1).1 r).hasDerivAt
  have htail := halfLineGreenTail_hasDerivAt
    monopoleRemainderSource_continuous monopoleRemainderSource_integrable hr
  have hmodel := (hlog.add (haff.const_mul monopoleAffineSlope)).add htail
  simp only [← sub_eq_add_neg] at hmodel
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact (monopoleProfile_hasDerivAt hx).deriv

theorem monopoleProfile_deriv_continuousOn :
    ContinuousOn (deriv monopoleProfile) (Ioi (0 : ℝ)) := by
  intro r hr
  exact (monopoleProfile_second_hasDerivAt hr).continuousAt.continuousWithinAt

theorem monopoleProfile_secondDeriv_continuousOn :
    ContinuousOn (deriv (deriv monopoleProfile)) (Ioi (0 : ℝ)) := by
  have hlog1 : ContDiff ℝ ∞ (deriv monopoleLogModel) :=
    (contDiff_infty_iff_deriv.mp monopoleLogModel_contDiff_infty).2
  have haff1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).2
  have hlog2 : Continuous (deriv (deriv monopoleLogModel)) :=
    (contDiff_infty_iff_deriv.mp hlog1).2.continuous
  have haff2 : Continuous (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp haff1).2.continuous
  have hcont := (hlog2.add (haff2.const_mul monopoleAffineSlope)).sub
    monopoleRemainderSource_continuous
  apply hcont.continuousOn.congr
  intro r hr
  exact (monopoleProfile_second_hasDerivAt hr).deriv

/-- The assembled profile solves the actual original half-line equation. -/
theorem monopoleProfile_hPlus_equation
    {r : ℝ} (hr : 0 < r) :
    hPlusApply monopoleProfile r = monopoleSource r := by
  have hsecond : deriv (deriv monopoleProfile) r =
      deriv (deriv monopoleLogModel) r +
        monopoleAffineSlope * deriv (deriv model) r +
          deriv (deriv monopoleRemainder) r := by
    rw [(monopoleProfile_second_hasDerivAt hr).deriv,
      (monopoleRemainder_second_hasDerivAt hr).deriv]
    ring
  calc
    hPlusApply monopoleProfile r =
        hPlusApply monopoleLogModel r +
          monopoleAffineSlope * hPlusApply model r +
            hPlusApply monopoleRemainder r := by
      unfold hPlusApply
      rw [hsecond, nonlocalApply_monopoleProfile hr.le]
      unfold monopoleProfile
      ring
    _ = monopoleSource r := by
      rw [monopoleRemainder_hPlus_equation hr]
      unfold monopoleCorrectedSource monopoleSource
      ring

theorem monopoleRadialProfile_hasDerivAt
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt monopoleRadialProfile
      (((deriv monopoleLogModel r + monopoleAffineSlope * deriv model r +
          halfLineGreenTail monopoleRemainderSource r) * r -
        monopoleProfile r) / r ^ 2) r := by
  convert (monopoleProfile_hasDerivAt hr).div (hasDerivAt_id r) hr.ne' using 1
  · funext x
    rfl
  · simp only [id_eq, mul_one]

end HBL.Modulation.Monopole
