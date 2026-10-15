import HBL.ScaledBubbleModulation

/-!
Local modulation at an arbitrary phased stationary bubble.

A fixed phase rotation is a continuous linear equivalence on the complex
radial dot-H1 energy model.  It sends exp(i*gamma0) W[a0] to the real
bubble W[a0].  Therefore the already verified scaled-bubble chart pulls
back to the phased bubble with all properties preserved:
C1 dependence, positive relative scale, the two tested equations, and
local uniqueness.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Local relative modulation coordinates around exp(i gamma0) W[a0].
The output is (rho, delta), where rho>0 is relative scale and delta is
relative phase. Absolute parameters are
  lambda = exp(a0) * rho,
  gamma  = gamma0 + delta.
-/
theorem radialDotH1_phasedBubble_relative_local_modulation
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
    ∃ Phi : ComplexRadialDotH1 → Param,
      Phi (phasedBubbleRadialDotH1 a₀ gamma₀) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi
        (phasedBubbleRadialDotH1 a₀ gamma₀) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝 (phasedBubbleRadialDotH1 a₀ gamma₀),
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
            (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝
        (phasedBubbleRadialDotH1 a₀ gamma₀, (0 : Param)),
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
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  obtain ⟨Psi, hPsi0, hPsiC1, hPos, hSolve, hUnique⟩ :=
    radialDotH1_scaledBubble_local_modulation
      R₀ hR₀ zPlus zMinus hzPlus hzMinus hzPlusR₀
      hPlusNorm hMinusNorm a₀
  let Rot : ComplexRadialDotH1 ≃L[ℝ] ComplexRadialDotH1 :=
    phaseRotationCLE (E := RadialDotH1) gamma₀
  let u₀ : ComplexRadialDotH1 :=
    phasedBubbleRadialDotH1 a₀ gamma₀
  let w₀ : ComplexRadialDotH1 :=
    (bubbleAtLogScaleRadialDotH1 a₀, (0 : RadialDotH1))
  have hRotBase : Rot u₀ = w₀ := by
    simpa [Rot, u₀, w₀] using
      phaseRotationCLE_phasedBubble a₀ gamma₀
  let Phi : ComplexRadialDotH1 → Param :=
    fun u => Psi (Rot u)
  have hPhi0 : Phi u₀ = (1, 0) := by
    simpa [Phi, hRotBase, w₀] using hPsi0
  have hRotC1 : ContDiffAt ℝ 1 (fun u : ComplexRadialDotH1 => Rot u) u₀ :=
    Rot.toContinuousLinearMap.contDiff.contDiffAt
  have hPsiC1' : ContDiffAt ℝ 1 Psi (Rot u₀) := by
    simpa [hRotBase] using hPsiC1
  have hPhiC1 : ContDiffAt ℝ 1 Phi u₀ := by
    exact hPsiC1'.comp u₀ hRotC1
  have hPhiPos : ∀ u, 0 < (Phi u).1 := by
    intro u
    exact hPos (Rot u)
  have hRotTendsto :
      Tendsto (fun u : ComplexRadialDotH1 => Rot u)
        (𝓝 u₀) (𝓝 w₀) := by
    have h :
        Tendsto (fun u : ComplexRadialDotH1 => Rot u)
          (𝓝 u₀) (𝓝 (Rot u₀)) :=
      Rot.continuous.continuousAt
    simpa [hRotBase] using h
  have hSolve' :=
    hRotTendsto.eventually hSolve
  let RotPair :
      (ComplexRadialDotH1 × Param) →
        (ComplexRadialDotH1 × Param) :=
    fun v => (Rot v.1, v.2)
  have hRotPairCont : Continuous RotPair := by
    dsimp [RotPair]
    exact (Rot.continuous.comp continuous_fst).prodMk continuous_snd
  have hRotPairBase :
      RotPair (u₀, (0 : Param)) = (w₀, (0 : Param)) := by
    simp [RotPair, hRotBase]
  have hRotPairTendsto :
      Tendsto RotPair
        (𝓝 (u₀, (0 : Param)))
        (𝓝 (w₀, (0 : Param))) := by
    have h :
        Tendsto RotPair
          (𝓝 (u₀, (0 : Param)))
          (𝓝 (RotPair (u₀, (0 : Param)))) :=
      hRotPairCont.continuousAt
    simpa [hRotPairBase] using h
  have hUnique' :=
    hRotPairTendsto.eventually hUnique
  refine ⟨Phi, ?_, ?_, hPhiPos, ?_, ?_⟩
  · simpa [u₀] using hPhi0
  · simpa [u₀] using hPhiC1
  · filter_upwards [hSolve'] with u hu
    simpa [Phi, Rot, w₀] using hu
  · filter_upwards [hUnique'] with v hv
    simpa [Phi, Rot, RotPair, w₀] using hv

end HBL.Modulation
