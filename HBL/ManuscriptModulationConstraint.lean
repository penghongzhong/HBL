import HBL.CompactSupportTransport

/-!
Manuscript-level interpretation of the verified standard-bubble modulation map.

The abstract state type RadialDotH1 is the full half-line L2 energy
coordinate q=(r f)'.  The first theorem restates the already verified
full-half-line implicit-function result in that notation.

The second theorem verifies, on smooth finite-energy radial profiles,
that the formal scalePhaseResidual is exactly the pair of threshold
constraints written in the manuscript after moving the scale pullback
onto the compact tests.  Compact support is used only to replace the
moving transformed endpoint by the fixed Hilbert cutoff R.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- The two manuscript orthogonality equations, written in real/imaginary
radial components after the phase rotation. -/
def manuscriptSmoothResidual
    (S : ℝ) (zPlus zMinus : ℝ → ℝ)
    (uRe uIm : ℝ → ℝ) (a gamma : ℝ) : Param :=
  (Real.cos gamma *
        compactThresholdPairing S zPlus (scalePullback uRe a) +
      Real.sin gamma *
        compactThresholdPairing S zPlus (scalePullback uIm a) -
      compactThresholdPairing S zPlus bubble,
    -Real.sin gamma *
        compactThresholdPairing S zMinus (scalePullback uRe a) +
      Real.cos gamma *
        compactThresholdPairing S zMinus (scalePullback uIm a))

/-- On smooth finite-energy radial data, the formal Hilbert residual is
exactly the manuscript's pair of compact threshold equations. -/
theorem scalePhaseResidual_on_smoothCore_eq_manuscript
    (S R : ℝ) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hcover : Real.exp 1 * S ≤ R)
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
    (a gamma : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
    scalePhaseResidual
      (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
      (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
      fullBubbleRadialEnergyL2
      ((smoothToRadialDotH1 uRe hmemRe,
          smoothToRadialDotH1 uIm hmemIm), (a, gamma)) =
      manuscriptSmoothResidual S zPlus zMinus uRe uIm a gamma := by
  have hPR :=
    fullTransportedEnergyThresholdDual_on_smoothCore
      R hR zPlus uRe hzPlus huRe hmemRe a
  have hPI :=
    fullTransportedEnergyThresholdDual_on_smoothCore
      R hR zPlus uIm hzPlus huIm hmemIm a
  have hMR :=
    fullTransportedEnergyThresholdDual_on_smoothCore
      R hR zMinus uRe hzMinus huRe hmemRe a
  have hMI :=
    fullTransportedEnergyThresholdDual_on_smoothCore
      R hR zMinus uIm hzMinus huIm hmemIm a
  have hPR' :
      fullTransportedEnergyThresholdDual R hR zPlus hzPlus a
          (smoothToRadialDotH1 uRe hmemRe) =
        compactThresholdPairing S zPlus (scalePullback uRe a) := by
    rw [hPR]
    exact transportedRadialTestIntegral_eq_compactThresholdPairing_of_support
      S R hS hcover zPlus uRe hzPlus.continuous huRe.continuous
      hsuppPlus a ha
  have hPI' :
      fullTransportedEnergyThresholdDual R hR zPlus hzPlus a
          (smoothToRadialDotH1 uIm hmemIm) =
        compactThresholdPairing S zPlus (scalePullback uIm a) := by
    rw [hPI]
    exact transportedRadialTestIntegral_eq_compactThresholdPairing_of_support
      S R hS hcover zPlus uIm hzPlus.continuous huIm.continuous
      hsuppPlus a ha
  have hMR' :
      fullTransportedEnergyThresholdDual R hR zMinus hzMinus a
          (smoothToRadialDotH1 uRe hmemRe) =
        compactThresholdPairing S zMinus (scalePullback uRe a) := by
    rw [hMR]
    exact transportedRadialTestIntegral_eq_compactThresholdPairing_of_support
      S R hS hcover zMinus uRe hzMinus.continuous huRe.continuous
      hsuppMinus a ha
  have hMI' :
      fullTransportedEnergyThresholdDual R hR zMinus hzMinus a
          (smoothToRadialDotH1 uIm hmemIm) =
        compactThresholdPairing S zMinus (scalePullback uIm a) := by
    rw [hMI]
    exact transportedRadialTestIntegral_eq_compactThresholdPairing_of_support
      S R hS hcover zMinus uIm hzMinus.continuous huIm.continuous
      hsuppMinus a ha
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hBP :
      fullTransportedEnergyThresholdDual R hR zPlus hzPlus 0
          fullBubbleRadialEnergyL2 =
        compactThresholdPairing S zPlus bubble := by
    rw [← smoothBubbleToRadialDotH1_eq]
    rw [fullTransportedEnergyThresholdDual_on_smoothCore
      R hR zPlus bubble hzPlus bubble_contDiff radialU_bubble_deriv_memLp 0]
    have ht :=
      transportedRadialTestIntegral_eq_compactThresholdPairing_of_support
        S R hS hcover zPlus bubble hzPlus.continuous
        bubble_contDiff.continuous hsuppPlus 0 hzero
    simpa [scalePullback] using ht
  unfold scalePhaseResidual scalePhaseObservable manuscriptSmoothResidual
  simp only [Prod.fst, Prod.snd, map_zero, mul_zero, add_zero,
    Real.cos_zero, Real.sin_zero, one_mul, neg_zero]
  rw [hPR', hPI', hMR', hMI', hBP]

/-- Standard-bubble local dynamic modulation in the concrete radial
homogeneous-energy model.  This is the full Banach/Hilbert implicit-function
conclusion at W; transfer to an arbitrary bubble is handled separately by
the scale-phase symmetry. -/
theorem radialDotH1_standard_local_modulation
    (R : ℝ) (hR : 0 ≤ R)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (hzPlusR : zPlus R = 0)
    (hPlusNorm :
      (∫ r in (0 : ℝ)..R,
        zPlus r * radialResonancePlus r) = 1)
    (hMinusNorm :
      (∫ r in (0 : ℝ)..R,
        zMinus r * radialResonanceMinus r) = 1) :
    ∃ Phi : ComplexRadialDotH1 → Param,
      Phi (fullBubbleRadialEnergyL2, (0 : RadialDotH1)) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi
        (fullBubbleRadialEnergyL2, (0 : RadialDotH1)) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝
        (fullBubbleRadialEnergyL2, (0 : RadialDotH1)),
        scalePhaseResidual
          (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
          (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
          fullBubbleRadialEnergyL2
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝
        ((fullBubbleRadialEnergyL2, (0 : RadialDotH1)),
          (0 : Param)),
        (scalePhaseResidual
          (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
          (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
          fullBubbleRadialEnergyL2 v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  exact fullRadialEnergy_local_modulation
    R hR zPlus zMinus hzPlus hzMinus hzPlusR hPlusNorm hMinusNorm

end HBL.Modulation
