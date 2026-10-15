import HBL.ArbitraryBubbleSmoothConstraint

/-!
Certification interface for the manuscript's first numbered lemma.

All analytic pieces have already been verified:
* radial dot-H1 Hilbert realization;
* continuity and C1 operator-norm regularity of compact tests;
* exact transported-test / manuscript-test identities;
* the explicit bubble and its scaled/phased orbit;
* the normalized -I2 Jacobian;
* the Banach-space implicit-function theorem with local uniqueness.

The manuscript's proof uses the finite-dimensional IFT, so the mathematically
correct uniqueness conclusion is local in the parameter variables.  The
theorem below states exactly that conclusion in absolute physical parameters.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- The actual standard-bubble parameter Jacobian for the concrete full
radial dot-H1 threshold functionals is the negative identity. -/
theorem manuscript_standardBubble_jacobian_eq_negId
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
    (fderiv ℝ
      (scalePhaseResidual
        (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
        (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
        fullBubbleRadialEnergyL2)
      ((fullBubbleRadialEnergyL2, (0 : RadialDotH1)),
        (0 : Param))).comp
      (ContinuousLinearMap.inr ℝ ComplexRadialDotH1 Param) =
        parameterNegId := by
  let Splus : ℝ → (RadialDotH1 →L[ℝ] ℝ) :=
    fullTransportedEnergyThresholdDual R hR zPlus hzPlus
  let Sminus : ℝ → (RadialDotH1 →L[ℝ] ℝ) :=
    fullTransportedEnergyThresholdDual R hR zMinus hzMinus
  let w : RadialDotH1 := fullBubbleRadialEnergyL2
  have hPlusC1 : ContDiffAt ℝ 1 Splus 0 := by
    simpa [Splus] using
      fullTransportedEnergyThresholdDual_contDiffAt_zero
        R hR zPlus hzPlus
  have hMinusC1 : ContDiffAt ℝ 1 Sminus 0 := by
    simpa [Sminus] using
      fullTransportedEnergyThresholdDual_contDiffAt_zero
        R hR zMinus hzMinus
  have hScale :
      HasDerivAt (fun a : ℝ => Splus a w) (-1) 0 := by
    simpa [Splus, w] using
      fullTransportedEnergyThresholdDual_bubble_hasDerivAt_of_restrict
        R hR zPlus hzPlus hzPlusR hPlusNorm
        fullBubbleRadialEnergyL2
        (fullBubbleRadialEnergyL2_restrict R hR)
  have hPhase : Sminus 0 w = 1 := by
    simpa [Sminus, w] using
      fullTransportedEnergyThresholdDual_bubble_zero_eq_one_of_restrict
        R hR zMinus hzMinus hMinusNorm
        fullBubbleRadialEnergyL2
        (fullBubbleRadialEnergyL2_restrict R hR)
  simpa [Splus, Sminus, w] using
    scalePhaseResidual_partial_jacobian
      Splus Sminus w hPlusC1 hMinusC1 hScale hPhase

/-- Correct local-uniqueness formulation of the manuscript's local dynamic
modulation lemma at an arbitrary phased/scaled bubble.  Compact support
hypotheses are included exactly so the Hilbert residual is the continuous
extension of the manuscript threshold equations on the smooth core. -/
theorem manuscript_modulation_local_corrected
    (S R₀ : ℝ) (hS : 0 ≤ S) (hR₀ : 0 ≤ R₀)
    (hSR : S ≤ R₀)
    (_hcover : Real.exp 1 * S ≤ R₀)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (hsuppPlus : ∀ y : ℝ, S ≤ y → zPlus y = 0)
    (_hsuppMinus : ∀ y : ℝ, S ≤ y → zMinus y = 0)
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
  have hzPlusR₀ : zPlus R₀ = 0 :=
    hsuppPlus R₀ hSR
  exact radialDotH1_phasedBubble_absolute_local_modulation
    R₀ hR₀ zPlus zMinus hzPlus hzMinus hzPlusR₀
    hPlusNorm hMinusNorm a₀ gamma₀

end HBL.Modulation
