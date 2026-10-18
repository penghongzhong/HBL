import HBL.WeightedHartreePointwiseContinuous
import HBL.MonopoleFredholmTail

/-!
Classical regularity of the concrete normalized monopole Fredholm solution.
The actual integral representative is twice differentiable at each positive
radius and satisfies the original half-line differential-integral equation.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem hPlusApply_continuous_of_contDiff_weighted_memLp
    (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q)
    (hmem : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure) :
    Continuous (hPlusApply q) := by
  have hq1 : ContDiff ℝ ∞ (deriv q) := (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv q)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  unfold hPlusApply
  exact (hq2.continuous.neg.sub
    ((potential_continuous.const_mul 3).mul hq.continuous)).sub
      (nonlocalApply_continuous_of_weighted_memLp q hmem)

theorem monopoleCorrectedSource_continuous (ell : ℝ) :
    Continuous (monopoleCorrectedSource ell) := by
  have hlog := hPlusApply_continuous_of_contDiff_weighted_memLp
    monopoleLogModel monopoleLogModel_contDiff_infty weightedLogModel_memLp_two
  have haff := hPlusApply_continuous_of_contDiff_weighted_memLp
    model model_contDiff_infty weightedAffineModel_memLp_two
  unfold monopoleCorrectedSource
  exact ((continuous_id.mul (bubble_contDiff_infty.continuous.pow 3)).sub
    hlog).sub (haff.const_mul ell)

theorem nonlocalApply_monopoleRemainder_continuous :
    Continuous (nonlocalApply monopoleRemainder) :=
  nonlocalApply_continuous_of_weighted_memLp
    monopoleRemainder monopoleRemainder_weighted_memLp_two

theorem monopoleRemainderSource_continuous :
    Continuous monopoleRemainderSource := by
  unfold monopoleRemainderSource
  exact ((monopoleCorrectedSource_continuous monopoleAffineSlope).add
    (((weightedGreenDecay_continuous.pow 2).const_mul 9).mul
      monopoleRemainder_continuous)).add
        nonlocalApply_monopoleRemainder_continuous

theorem monopoleRemainder_hasDerivAt
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt monopoleRemainder
      (halfLineGreenTail monopoleRemainderSource r) r := by
  have hrep : monopoleRemainder = halfLineMinGreen monopoleRemainderSource :=
    funext monopoleRemainder_eq_halfLineMinGreen
  rw [hrep]
  exact halfLineMinGreen_hasDerivAt monopoleRemainderSource_continuous
    monopoleRemainderSource_integrable hr

theorem monopoleRemainder_second_hasDerivAt
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv monopoleRemainder) (-monopoleRemainderSource r) r := by
  have hrep : monopoleRemainder = halfLineMinGreen monopoleRemainderSource :=
    funext monopoleRemainder_eq_halfLineMinGreen
  rw [hrep]
  exact halfLineMinGreen_second_hasDerivAt monopoleRemainderSource_continuous
    monopoleRemainderSource_integrable hr

theorem monopoleRemainder_deriv_continuousOn :
    ContinuousOn (deriv monopoleRemainder) (Ioi (0 : ℝ)) := by
  intro r hr
  exact (monopoleRemainder_second_hasDerivAt hr).continuousAt.continuousWithinAt

theorem monopoleRemainder_secondDeriv_continuousOn :
    ContinuousOn (deriv (deriv monopoleRemainder)) (Ioi (0 : ℝ)) := by
  apply monopoleRemainderSource_continuous.neg.continuousOn.congr
  intro r hr
  exact (monopoleRemainder_second_hasDerivAt hr).deriv

/-- The actual classical half-line equation for the constructed remainder. -/
theorem monopoleRemainder_hPlus_equation
    {r : ℝ} (hr : 0 < r) :
    hPlusApply monopoleRemainder r =
      monopoleCorrectedSource monopoleAffineSlope r := by
  unfold hPlusApply
  rw [(monopoleRemainder_second_hasDerivAt hr).deriv]
  unfold monopoleRemainderSource potential weightedGreenDecay
  field_simp [show (1 + r ^ 2 : ℝ) ≠ 0 by positivity]
  ring

end HBL.Modulation.Monopole
