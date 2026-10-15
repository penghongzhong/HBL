import HBL.ArbitraryBubbleBridgeCore

/-!
Exact smooth-core identification of the arbitrary-bubble absolute residual
with the manuscript's two threshold equations.

For positive absolute parameters (lambda,gamma), set
  b     = log(lambda)-a0,
  delta = gamma-gamma0.
The fixed phase rotation and the relative phase combine to gamma, while the
centered compact-support theorem identifies the shifted Hilbert dual with
ell_zeta(T_{lambda,0} f).  The base subtraction is exactly ell_+(W),0.

Thus the abstract/Hilbert residual is not merely analogous to the manuscript
constraint: on the smooth finite-energy radial core it is exactly the same
pair of scalar equations.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace HBL.Modulation

theorem phasedAbsoluteResidual_on_smoothCore_eq_manuscript
    (S R₀ : ℝ) (hS : 0 ≤ S) (hR₀ : 0 ≤ R₀)
    (hcover : Real.exp 1 * S ≤ R₀)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (hsuppPlus : ∀ y : ℝ, S ≤ y → zPlus y = 0)
    (hsuppMinus : ∀ y : ℝ, S ≤ y → zMinus y = 0)
    (uRe uIm : ℝ → ℝ)
    (huRe : ContDiff ℝ 1 uRe)
    (huIm : ContDiff ℝ 1 uIm)
    (hmemRe : MemLp (deriv (radialU uRe)) 2
      (volume.restrict (Ioi (0 : ℝ))))
    (hmemIm : MemLp (deriv (radialU uIm)) 2
      (volume.restrict (Ioi (0 : ℝ))))
    (a₀ gamma₀ : ℝ) (p : Param)
    (_hp : 0 < p.1)
    (hb : Real.log p.1 - a₀ ∈ Icc (-1 : ℝ) 1) :
    phasedAbsoluteResidual
      R₀ hR₀ zPlus zMinus hzPlus hzMinus a₀ gamma₀
      (smoothToRadialDotH1 uRe hmemRe,
        smoothToRadialDotH1 uIm hmemIm) p =
    manuscriptSmoothResidual
      S zPlus zMinus uRe uIm (Real.log p.1) p.2 := by
  let b : ℝ := Real.log p.1 - a₀
  let delta : ℝ := p.2 - gamma₀
  let Rcut : ℝ := Real.exp (-a₀) * R₀
  let hRcut : 0 ≤ Rcut :=
    scaledBubbleCutoff_nonneg R₀ a₀ hR₀
  let Splus : ℝ → (RadialDotH1 →L[ℝ] ℝ) :=
    fun x =>
      fullTransportedEnergyThresholdDual
        Rcut hRcut zPlus hzPlus (a₀ + x)
  let Sminus : ℝ → (RadialDotH1 →L[ℝ] ℝ) :=
    fun x =>
      fullTransportedEnergyThresholdDual
        Rcut hRcut zMinus hzMinus (a₀ + x)
  let w : RadialDotH1 := bubbleAtLogScaleRadialDotH1 a₀
  let qRe : RadialDotH1 := smoothToRadialDotH1 uRe hmemRe
  let qIm : RadialDotH1 := smoothToRadialDotH1 uIm hmemIm
  have hb' : b ∈ Icc (-1 : ℝ) 1 := by
    simpa [b] using hb
  have hab : a₀ + b = Real.log p.1 := by
    dsimp [b]
    ring
  have hgamma : gamma₀ + delta = p.2 := by
    dsimp [delta]
    ring
  have hPR :
      Splus b qRe =
        compactThresholdPairing S zPlus
          (scalePullback uRe (Real.log p.1)) := by
    dsimp [Splus, qRe, Rcut, hRcut]
    rw [fullTransportedEnergyThresholdDual_on_smoothCore
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zPlus uRe hzPlus huRe hmemRe (a₀ + b)]
    have ht :=
      transportedRadialTestIntegral_centered_eq_compactThresholdPairing
        S R₀ hS hcover zPlus uRe
        hzPlus.continuous huRe.continuous hsuppPlus a₀ b hb'
    rw [hab] at ht
    exact ht
  have hPI :
      Splus b qIm =
        compactThresholdPairing S zPlus
          (scalePullback uIm (Real.log p.1)) := by
    dsimp [Splus, qIm, Rcut, hRcut]
    rw [fullTransportedEnergyThresholdDual_on_smoothCore
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zPlus uIm hzPlus huIm hmemIm (a₀ + b)]
    have ht :=
      transportedRadialTestIntegral_centered_eq_compactThresholdPairing
        S R₀ hS hcover zPlus uIm
        hzPlus.continuous huIm.continuous hsuppPlus a₀ b hb'
    rw [hab] at ht
    exact ht
  have hMR :
      Sminus b qRe =
        compactThresholdPairing S zMinus
          (scalePullback uRe (Real.log p.1)) := by
    dsimp [Sminus, qRe, Rcut, hRcut]
    rw [fullTransportedEnergyThresholdDual_on_smoothCore
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zMinus uRe hzMinus huRe hmemRe (a₀ + b)]
    have ht :=
      transportedRadialTestIntegral_centered_eq_compactThresholdPairing
        S R₀ hS hcover zMinus uRe
        hzMinus.continuous huRe.continuous hsuppMinus a₀ b hb'
    rw [hab] at ht
    exact ht
  have hMI :
      Sminus b qIm =
        compactThresholdPairing S zMinus
          (scalePullback uIm (Real.log p.1)) := by
    dsimp [Sminus, qIm, Rcut, hRcut]
    rw [fullTransportedEnergyThresholdDual_on_smoothCore
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zMinus uIm hzMinus huIm hmemIm (a₀ + b)]
    have ht :=
      transportedRadialTestIntegral_centered_eq_compactThresholdPairing
        S R₀ hS hcover zMinus uIm
        hzMinus.continuous huIm.continuous hsuppMinus a₀ b hb'
    rw [hab] at ht
    exact ht
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by
    norm_num
  have hBP :
      Splus 0 w =
        compactThresholdPairing S zPlus bubble := by
    dsimp [Splus, w, Rcut, hRcut]
    unfold bubbleAtLogScaleRadialDotH1
    rw [fullTransportedEnergyThresholdDual_on_smoothCore
      (Real.exp (-a₀) * R₀)
      (scaledBubbleCutoff_nonneg R₀ a₀ hR₀)
      zPlus (bubbleAtLogScale a₀) hzPlus
      (bubbleAtLogScale_contDiff a₀)
      (radialU_bubbleAtLogScale_deriv_memLp a₀) a₀]
    have hrec :=
      transportedRadialTestIntegral_scaledBubble_recenter
        R₀ zPlus a₀ 0
    have hs :=
      transportedRadialTestIntegral_eq_compactThresholdPairing_of_support
        S R₀ hS hcover zPlus bubble
        hzPlus.continuous bubble_contDiff.continuous
        hsuppPlus 0 hzero
    simpa using hrec.trans hs
  have hCurrent :
      scalePhaseObservable Splus Sminus
        ((qRe, qIm), (b, gamma₀ + delta)) =
      (Real.cos p.2 *
          compactThresholdPairing S zPlus
            (scalePullback uRe (Real.log p.1)) +
        Real.sin p.2 *
          compactThresholdPairing S zPlus
            (scalePullback uIm (Real.log p.1)),
       -Real.sin p.2 *
          compactThresholdPairing S zMinus
            (scalePullback uRe (Real.log p.1)) +
        Real.cos p.2 *
          compactThresholdPairing S zMinus
            (scalePullback uIm (Real.log p.1))) := by
    unfold scalePhaseObservable
    change
      (Real.cos (gamma₀ + delta) * Splus b qRe +
          Real.sin (gamma₀ + delta) * Splus b qIm,
       -Real.sin (gamma₀ + delta) * Sminus b qRe +
          Real.cos (gamma₀ + delta) * Sminus b qIm) = _
    rw [hgamma, hPR, hPI, hMR, hMI]
  have hBase :
      scalePhaseObservable Splus Sminus
        ((w, (0 : RadialDotH1)), (0 : Param)) =
      (compactThresholdPairing S zPlus bubble, 0) := by
    rw [scalePhaseObservable_real_state]
    change
      (Real.cos 0 * Splus 0 w,
        -Real.sin 0 * Sminus 0 w) =
      (compactThresholdPairing S zPlus bubble, 0)
    simp [hBP]
  have hcoord :
      absolutePhysicalToRelativeLog a₀ gamma₀ p = (b, delta) := by
    rfl
  unfold phasedAbsoluteResidual
  change scalePhaseResidual Splus Sminus w
      (phaseRotationCLE (E := RadialDotH1) gamma₀ (qRe, qIm),
        absolutePhysicalToRelativeLog a₀ gamma₀ p) =
    manuscriptSmoothResidual
      S zPlus zMinus uRe uIm (Real.log p.1) p.2
  rw [hcoord]
  rw [scalePhaseResidual_phaseRotation_add
    Splus Sminus w (qRe, qIm) b gamma₀ delta]
  rw [hCurrent, hBase]
  simp [manuscriptSmoothResidual]

end HBL.Modulation
