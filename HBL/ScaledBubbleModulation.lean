import HBL.ScaledBubbleTestIdentity

/-!
Local modulation at an arbitrary stationary-bubble scale.

The full operator-norm C1 test family is translated from absolute
logarithmic scale a=a0+b to the relative coordinate b=0.  The exact
scale derivative -1 and phase normalization 1 at W[a0] were verified
in ScaledBubbleTestIdentity.  Therefore the generic Banach-space
implicit-function theorem applies without any new analytic hypothesis.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Local modulation at the real stationary bubble W[a0].
The first output coordinate is the positive relative scale rho=exp b;
the corresponding absolute logarithmic scale is a0+log rho. -/
theorem radialDotH1_scaledBubble_local_modulation
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (hzPlusR₀ : zPlus R₀ = 0)
    (hPlusNorm :
      (∫ r in (0 : ℝ)..R₀,
        zPlus r * radialResonancePlus r) = 1)
    (hMinusNorm :
      (∫ r in (0 : ℝ)..R₀,
        zMinus r * radialResonanceMinus r) = 1)
    (a₀ : ℝ) :
    ∃ Phi : ComplexRadialDotH1 → Param,
      Phi (bubbleAtLogScaleRadialDotH1 a₀,
        (0 : RadialDotH1)) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi
        (bubbleAtLogScaleRadialDotH1 a₀,
          (0 : RadialDotH1)) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝
        (bubbleAtLogScaleRadialDotH1 a₀,
          (0 : RadialDotH1)),
        scalePhaseResidual
          (fun b : ℝ =>
            fullTransportedEnergyThresholdDual
              (Real.exp (-a₀) * R₀)
              (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
              zPlus hzPlus (a₀ + b))
          (fun b : ℝ =>
            fullTransportedEnergyThresholdDual
              (Real.exp (-a₀) * R₀)
              (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
              zMinus hzMinus (a₀ + b))
          (bubbleAtLogScaleRadialDotH1 a₀)
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝
        ((bubbleAtLogScaleRadialDotH1 a₀,
            (0 : RadialDotH1)), (0 : Param)),
        (scalePhaseResidual
          (fun b : ℝ =>
            fullTransportedEnergyThresholdDual
              (Real.exp (-a₀) * R₀)
              (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
              zPlus hzPlus (a₀ + b))
          (fun b : ℝ =>
            fullTransportedEnergyThresholdDual
              (Real.exp (-a₀) * R₀)
              (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
              zMinus hzMinus (a₀ + b))
          (bubbleAtLogScaleRadialDotH1 a₀) v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  let Splus : ℝ → (RadialDotH1 →L[ℝ] ℝ) :=
    fun b =>
      fullTransportedEnergyThresholdDual
        (Real.exp (-a₀) * R₀)
        (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
        zPlus hzPlus (a₀ + b)
  let Sminus : ℝ → (RadialDotH1 →L[ℝ] ℝ) :=
    fun b =>
      fullTransportedEnergyThresholdDual
        (Real.exp (-a₀) * R₀)
        (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
        zMinus hzMinus (a₀ + b)
  let w : RadialDotH1 :=
    bubbleAtLogScaleRadialDotH1 a₀
  have hPlusC1 : ContDiffAt ℝ 1 Splus 0 := by
    simpa [Splus] using
      shiftedFullTransportedEnergyThresholdDual_contDiffAt_zero
        R₀ hR₀ zPlus hzPlus a₀
  have hMinusC1 : ContDiffAt ℝ 1 Sminus 0 := by
    simpa [Sminus] using
      shiftedFullTransportedEnergyThresholdDual_contDiffAt_zero
        R₀ hR₀ zMinus hzMinus a₀
  have hScale :
      HasDerivAt (fun b : ℝ => Splus b w) (-1) 0 := by
    simpa [Splus, w] using
      fullTransportedEnergyThresholdDual_scaledBubble_hasDerivAt
        R₀ hR₀ zPlus hzPlus hzPlusR₀ hPlusNorm a₀
  have hPhase : Sminus 0 w = 1 := by
    simpa [Sminus, w] using
      fullTransportedEnergyThresholdDual_scaledBubble_zero_eq_one
        R₀ hR₀ zMinus hzMinus hMinusNorm a₀
  simpa [Splus, Sminus, w] using
    scalePhase_local_modulation_physical
      Splus Sminus w hPlusC1 hMinusC1 hScale hPhase

end HBL.Modulation
