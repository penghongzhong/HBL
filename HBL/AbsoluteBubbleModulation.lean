import HBL.AbsoluteModulationParameters

/-!
Absolute physical local modulation at an arbitrary phased stationary bubble.

This module packages the verified relative chart into the manuscript's
physical parameters (lambda,gamma).  The residual is defined through the
bounded transported duals, which agree with the manuscript tests on the
smooth radial core.

Uniqueness is stated in the mathematically precise IFT form: among positive
physical parameters in a neighborhood of the base parameter
(exp(a0),gamma0).  This is the local uniqueness actually delivered by the
proof.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- The tested residual in absolute physical parameters near the phased
bubble exp(i gamma0) W[a0]. -/
def phasedAbsoluteResidual
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (a₀ gamma₀ : ℝ)
    (u : ComplexRadialDotH1) (p : Param) : Param :=
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
    (phaseRotationCLE (E := RadialDotH1) gamma₀ u,
      absolutePhysicalToRelativeLog a₀ gamma₀ p)

/-- Full local modulation theorem in absolute physical parameters around
an arbitrary phased stationary bubble. -/
theorem radialDotH1_phasedBubble_absolute_local_modulation
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
    (a₀ gamma₀ : ℝ) :
    ∃ LambdaGamma : ComplexRadialDotH1 → Param,
      LambdaGamma (phasedBubbleRadialDotH1 a₀ gamma₀) =
        (Real.exp a₀, gamma₀) ∧
      ContDiffAt ℝ 1 LambdaGamma
        (phasedBubbleRadialDotH1 a₀ gamma₀) ∧
      (∀ u, 0 < (LambdaGamma u).1) ∧
      (∀ᶠ u in 𝓝 (phasedBubbleRadialDotH1 a₀ gamma₀),
        phasedAbsoluteResidual
          R₀ hR₀ zPlus zMinus hzPlus hzMinus
          a₀ gamma₀ u (LambdaGamma u) = 0) ∧
      (∀ᶠ v in 𝓝
        (phasedBubbleRadialDotH1 a₀ gamma₀,
          (Real.exp a₀, gamma₀)),
        0 < v.2.1 →
          (phasedAbsoluteResidual
            R₀ hR₀ zPlus zMinus hzPlus hzMinus
            a₀ gamma₀ v.1 v.2 = 0 ↔
            LambdaGamma v.1 = v.2)) := by
  obtain ⟨Phi, hPhi0, hPhiC1, hPos, hSolve, hUnique⟩ :=
    radialDotH1_phasedBubble_relative_local_modulation
      R₀ hR₀ zPlus zMinus hzPlus hzMinus hzPlusR₀
      hPlusNorm hMinusNorm a₀ gamma₀
  let u₀ : ComplexRadialDotH1 :=
    phasedBubbleRadialDotH1 a₀ gamma₀
  let p₀ : Param := (Real.exp a₀, gamma₀)
  let LambdaGamma : ComplexRadialDotH1 → Param :=
    fun u => relativePhysicalToAbsolute a₀ gamma₀ (Phi u)
  have hLG0 : LambdaGamma u₀ = p₀ := by
    rw [show Phi u₀ = (1, 0) by simpa [u₀] using hPhi0]
    simp [LambdaGamma, p₀]
  have hMapC1 :
      ContDiffAt ℝ 1
        (relativePhysicalToAbsolute a₀ gamma₀)
        (Phi u₀) :=
    relativePhysicalToAbsolute_contDiffAt a₀ gamma₀ (Phi u₀)
  have hPhiC1' : ContDiffAt ℝ 1 Phi u₀ := by
    simpa [u₀] using hPhiC1
  have hLGC1 : ContDiffAt ℝ 1 LambdaGamma u₀ := by
    exact hMapC1.comp u₀ hPhiC1'
  have hLGPos : ∀ u, 0 < (LambdaGamma u).1 := by
    intro u
    exact relativePhysicalToAbsolute_scale_pos
      a₀ gamma₀ (Phi u) (hPos u)
  have hSolveAbs :
      ∀ᶠ u in 𝓝 u₀,
        phasedAbsoluteResidual
          R₀ hR₀ zPlus zMinus hzPlus hzMinus
          a₀ gamma₀ u (LambdaGamma u) = 0 := by
    have hSolve' : ∀ᶠ u in 𝓝 u₀,
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
          (phaseRotationCLE (E := RadialDotH1) gamma₀ u,
            (Real.log (Phi u).1, (Phi u).2)) = 0 := by
      simpa [u₀] using hSolve
    filter_upwards [hSolve'] with u hu
    have hcoord :=
      absolutePhysicalToRelativeLog_relative
        a₀ gamma₀ (Phi u) (hPos u)
    unfold phasedAbsoluteResidual
    change scalePhaseResidual
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
      (phaseRotationCLE (E := RadialDotH1) gamma₀ u,
        absolutePhysicalToRelativeLog a₀ gamma₀
          (relativePhysicalToAbsolute a₀ gamma₀ (Phi u))) = 0
    rw [hcoord]
    exact hu
  let ToRelativePair :
      (ComplexRadialDotH1 × Param) →
        (ComplexRadialDotH1 × Param) :=
    fun v =>
      (v.1, absolutePhysicalToRelativeLog a₀ gamma₀ v.2)
  have hp₀ne : p₀.1 ≠ 0 := by
    simp [p₀, Real.exp_ne_zero]
  have hParamC1 :
      ContDiffAt ℝ 1
        (absolutePhysicalToRelativeLog a₀ gamma₀) p₀ :=
    absolutePhysicalToRelativeLog_contDiffAt
      a₀ gamma₀ p₀ hp₀ne
  have hfstC1 :
      ContDiffAt ℝ 1
        (fun v : ComplexRadialDotH1 × Param => v.1)
        (u₀, p₀) :=
    (ContinuousLinearMap.fst ℝ ComplexRadialDotH1 Param).contDiff.contDiffAt
  have hsndC1 :
      ContDiffAt ℝ 1
        (fun v : ComplexRadialDotH1 × Param => v.2)
        (u₀, p₀) :=
    (ContinuousLinearMap.snd ℝ ComplexRadialDotH1 Param).contDiff.contDiffAt
  have hrelC1 :
      ContDiffAt ℝ 1
        (fun v : ComplexRadialDotH1 × Param =>
          absolutePhysicalToRelativeLog a₀ gamma₀ v.2)
        (u₀, p₀) :=
    hParamC1.comp (u₀, p₀) hsndC1
  have hPairC1 :
      ContDiffAt ℝ 1 ToRelativePair (u₀, p₀) := by
    exact hfstC1.prodMk hrelC1
  have hPairBase :
      ToRelativePair (u₀, p₀) = (u₀, (0 : Param)) := by
    apply Prod.ext
    · rfl
    · simp [ToRelativePair, p₀, absolutePhysicalToRelativeLog]
  have hPairTendsto :
      Tendsto ToRelativePair
        (𝓝 (u₀, p₀)) (𝓝 (u₀, (0 : Param))) := by
    have h :
        Tendsto ToRelativePair
          (𝓝 (u₀, p₀))
          (𝓝 (ToRelativePair (u₀, p₀))) :=
      hPairC1.continuousAt
    simpa [hPairBase] using h
  have hUniqueRel :
      ∀ᶠ v in 𝓝 (u₀, (0 : Param)),
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
          (bubbleAtLogScaleRadialDotH1 a₀)
          (phaseRotationCLE (E := RadialDotH1) gamma₀ v.1, v.2) = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2) := by
    simpa [u₀] using hUnique
  have hUniqueAbsRaw :=
    hPairTendsto.eventually hUniqueRel
  refine ⟨LambdaGamma, ?_, ?_, hLGPos, ?_, ?_⟩
  · simpa [u₀, p₀] using hLG0
  · simpa [u₀] using hLGC1
  · simpa [u₀] using hSolveAbs
  · filter_upwards [hUniqueAbsRaw] with v hv
    intro hvpos
    unfold phasedAbsoluteResidual
    have hiff :=
      relativeLog_eq_absoluteLog_iff
        a₀ gamma₀ (Phi v.1) v.2 (hPos v.1) hvpos
    change
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
        (bubbleAtLogScaleRadialDotH1 a₀)
        (phaseRotationCLE (E := RadialDotH1) gamma₀ v.1,
          absolutePhysicalToRelativeLog a₀ gamma₀ v.2) = 0 ↔
        relativePhysicalToAbsolute a₀ gamma₀ (Phi v.1) = v.2)
    exact hv.trans hiff

end HBL.Modulation
