import HBL.PhaseRotationEnergy

/-!
Exact recentering of the tested scalar integral at an arbitrary base scale.

For W[a0](r)=exp(a0/2)W(exp(a0)r) and the fixed Hilbert cutoff
  R[a0]=exp(-a0) R0,
a change of variables shows
  I_{R[a0]}(zeta,W[a0],a0+b)=I_{R0}(zeta,W,b).

Therefore the already verified normalizations at W give the exact scale
Jacobian -1 and phase value 1 at every scaled stationary bubble, without
constructing a global dilation operator on the ambient L2 space.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Exact fixed-radius change of variables from a scaled bubble back to W. -/
theorem transportedRadialTestIntegral_scaledBubble_recenter
    (R₀ : ℝ) (zeta : ℝ → ℝ) (a₀ b : ℝ) :
    transportedRadialTestIntegral
        (Real.exp (-a₀) * R₀) zeta
        (bubbleAtLogScale a₀) (a₀ + b) =
      transportedRadialTestIntegral R₀ zeta bubble b := by
  let F : ℝ → ℝ :=
    fun s => transportedRadialTest zeta b s * bubble s
  have hcv :=
    intervalIntegral.smul_integral_comp_mul_left
      F (Real.exp a₀)
      (a := (0 : ℝ)) (b := Real.exp (-a₀) * R₀)
  have hbound :
      Real.exp a₀ * (Real.exp (-a₀) * R₀) = R₀ := by
    calc
      Real.exp a₀ * (Real.exp (-a₀) * R₀) =
          (Real.exp a₀ * Real.exp (-a₀)) * R₀ := by ring
      _ = R₀ := by
        rw [← Real.exp_add]
        simp
  have hleft :
      (Real.exp a₀) •
          (∫ r in (0 : ℝ)..Real.exp (-a₀) * R₀,
            F (Real.exp a₀ * r)) =
        transportedRadialTestIntegral
          (Real.exp (-a₀) * R₀) zeta
          (bubbleAtLogScale a₀) (a₀ + b) := by
    rw [← intervalIntegral.integral_smul]
    unfold transportedRadialTestIntegral
    apply intervalIntegral.integral_congr
    intro r _
    change Real.exp a₀ *
        (transportedRadialTest zeta b (Real.exp a₀ * r) *
          bubble (Real.exp a₀ * r)) =
      transportedRadialTest zeta (a₀ + b) r *
        bubbleAtLogScale a₀ r
    unfold transportedRadialTest bubbleAtLogScale
    rw [Real.exp_add]
    have hthree :
        Real.exp ((3 / 2 : ℝ) * (a₀ + b)) =
          Real.exp ((3 / 2 : ℝ) * a₀) *
            Real.exp ((3 / 2 : ℝ) * b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hthree]
    have hscale :
        Real.exp a₀ * Real.exp a₀ =
          Real.exp ((3 / 2 : ℝ) * a₀) *
            Real.exp (a₀ / 2) := by
      calc
        Real.exp a₀ * Real.exp a₀ =
            Real.exp (a₀ + a₀) := by rw [Real.exp_add]
        _ = Real.exp ((3 / 2 : ℝ) * a₀ + a₀ / 2) := by
              congr 1
              ring
        _ = Real.exp ((3 / 2 : ℝ) * a₀) *
            Real.exp (a₀ / 2) := by rw [Real.exp_add]
    have harg :
        Real.exp b * (Real.exp a₀ * r) =
          Real.exp a₀ * Real.exp b * r := by ring
    rw [harg]
    calc
      Real.exp a₀ *
          (Real.exp ((3 / 2 : ℝ) * b) *
              zeta (Real.exp a₀ * Real.exp b * r) *
              (Real.exp a₀ * r) *
              bubble (Real.exp a₀ * r)) =
          (Real.exp a₀ * Real.exp a₀) *
            Real.exp ((3 / 2 : ℝ) * b) *
            zeta (Real.exp a₀ * Real.exp b * r) * r *
            bubble (Real.exp a₀ * r) := by ring
      _ = (Real.exp ((3 / 2 : ℝ) * a₀) *
            Real.exp (a₀ / 2)) *
            Real.exp ((3 / 2 : ℝ) * b) *
            zeta (Real.exp a₀ * Real.exp b * r) * r *
            bubble (Real.exp a₀ * r) := by rw [hscale]
      _ = Real.exp ((3 / 2 : ℝ) * a₀) *
            Real.exp ((3 / 2 : ℝ) * b) *
            zeta (Real.exp a₀ * Real.exp b * r) * r *
            (Real.exp (a₀ / 2) * bubble (Real.exp a₀ * r)) := by ring
  rw [hbound] at hcv
  rw [hleft] at hcv
  change transportedRadialTestIntegral
      (Real.exp (-a₀) * R₀) zeta
      (bubbleAtLogScale a₀) (a₀ + b) =
    ∫ s in (0 : ℝ)..R₀, F s
  simpa only [mul_zero] using hcv

/-- The finite cutoff used at a scaled bubble is nonnegative whenever R0 is. -/
theorem scaledBubbleCutoff_nonneg
    (R₀ a₀ : ℝ) (hR₀ : 0 ≤ R₀) :
    0 ≤ Real.exp (-a₀) * R₀ :=
  mul_nonneg (Real.exp_pos _).le hR₀

/-- The positive-channel tested value at W[a0], as a function of the
relative logarithmic parameter b, has derivative -1 at b=0. -/
theorem fullTransportedEnergyThresholdDual_scaledBubble_hasDerivAt
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hzetaR₀ : zeta R₀ = 0)
    (hNorm :
      (∫ r in (0 : ℝ)..R₀,
        zeta r * radialResonancePlus r) = 1)
    (a₀ : ℝ) :
    HasDerivAt
      (fun b : ℝ =>
        fullTransportedEnergyThresholdDual
          (Real.exp (-a₀) * R₀)
          (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
          zeta hzeta (a₀ + b)
          (bubbleAtLogScaleRadialDotH1 a₀))
      (-1) 0 := by
  have hscalar :=
    bubble_normalized_scale_integral
      R₀ hR₀ zeta hzeta hzetaR₀ hNorm
  have heq :
      (fun b : ℝ =>
        fullTransportedEnergyThresholdDual
          (Real.exp (-a₀) * R₀)
          (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
          zeta hzeta (a₀ + b)
          (bubbleAtLogScaleRadialDotH1 a₀)) =
      transportedRadialTestIntegral R₀ zeta bubble := by
    funext b
    unfold bubbleAtLogScaleRadialDotH1
    rw [fullTransportedEnergyThresholdDual_on_smoothCore
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zeta (bubbleAtLogScale a₀) hzeta
      (bubbleAtLogScale_contDiff a₀)
      (radialU_bubbleAtLogScale_deriv_memLp a₀)
      (a₀ + b)]
    exact transportedRadialTestIntegral_scaledBubble_recenter
      R₀ zeta a₀ b
  rw [heq]
  exact hscalar

/-- The negative-channel value at the scaled bubble and centered scale is one. -/
theorem fullTransportedEnergyThresholdDual_scaledBubble_zero_eq_one
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hNorm :
      (∫ r in (0 : ℝ)..R₀,
        zeta r * radialResonanceMinus r) = 1)
    (a₀ : ℝ) :
    fullTransportedEnergyThresholdDual
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zeta hzeta a₀
      (bubbleAtLogScaleRadialDotH1 a₀) = 1 := by
  unfold bubbleAtLogScaleRadialDotH1
  rw [fullTransportedEnergyThresholdDual_on_smoothCore
    (Real.exp (-a₀) * R₀)
    (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
    zeta (bubbleAtLogScale a₀) hzeta
    (bubbleAtLogScale_contDiff a₀)
    (radialU_bubbleAtLogScale_deriv_memLp a₀) a₀]
  have hrec :
      transportedRadialTestIntegral
          (Real.exp (-a₀) * R₀) zeta
          (bubbleAtLogScale a₀) a₀ =
        transportedRadialTestIntegral R₀ zeta bubble 0 := by
    simpa using
      transportedRadialTestIntegral_scaledBubble_recenter
        R₀ zeta a₀ 0
  rw [hrec, bubble_phase_pairing_at_zero]
  exact hNorm

/-- The shifted full threshold dual is C1 at relative parameter zero. -/
theorem shiftedFullTransportedEnergyThresholdDual_contDiffAt_zero
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ : ℝ) :
    ContDiffAt ℝ 1
      (fun b : ℝ =>
        fullTransportedEnergyThresholdDual
          (Real.exp (-a₀) * R₀)
          (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
          zeta hzeta (a₀ + b))
      0 := by
  have hbase :=
    fullTransportedEnergyThresholdDual_contDiffAt
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zeta hzeta a₀
  have hadd :
      ContDiffAt ℝ 1 (fun b : ℝ => a₀ + b) 0 := by
    fun_prop
  have hbase' :
      ContDiffAt ℝ 1
        (fullTransportedEnergyThresholdDual
          (Real.exp (-a₀) * R₀)
          (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
          zeta hzeta)
        (a₀ + 0) := by
    simpa using hbase
  have hcomp :=
    hbase'.comp (f := fun b : ℝ => a₀ + b) 0 hadd
  simpa [Function.comp_def] using hcomp

end HBL.Modulation
