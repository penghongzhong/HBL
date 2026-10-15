import HBL.TransportedEnergyC1

/-!
Finite-radius radial-energy assembly of the first modulation lemma.

All analytic inputs in this theorem are now the concrete corrected
transported threshold functionals:
* operator-norm C1 dependence on logarithmic scale;
* scale derivative -1 at the explicit stationary bubble;
* phase-channel normalization 1.

Thus the implicit-function conclusion is obtained with no abstract
Jacobian or dual-regularity hypothesis.  This theorem is intentionally
stated on the concrete finite-radius L2 radial-energy coordinate.  The
remaining manuscript-level task is to identify this model with the full
radial homogeneous-energy space using compact support of the two tests.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Finite-radius energy coordinate of the stationary bubble. -/
def bubbleRadialEnergyL2 (R : ℝ) (hR : 0 ≤ R) :
    RadialEnergyL2 R :=
  radialUDerivativeL2 R hR bubble bubble_contDiff

/-- The first manuscript modulation conclusion on the concrete
finite-radius radial energy Hilbert model. -/
theorem finiteRadialEnergy_local_modulation
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
    ∃ Phi : (RadialEnergyL2 R × RadialEnergyL2 R) → Param,
      Phi (bubbleRadialEnergyL2 R hR, (0 : RadialEnergyL2 R)) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi
        (bubbleRadialEnergyL2 R hR, (0 : RadialEnergyL2 R)) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝
        (bubbleRadialEnergyL2 R hR, (0 : RadialEnergyL2 R)),
        scalePhaseResidual
          (transportedEnergyThresholdDual R hR zPlus hzPlus)
          (transportedEnergyThresholdDual R hR zMinus hzMinus)
          (bubbleRadialEnergyL2 R hR)
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝
        ((bubbleRadialEnergyL2 R hR, (0 : RadialEnergyL2 R)),
          (0 : Param)),
        (scalePhaseResidual
          (transportedEnergyThresholdDual R hR zPlus hzPlus)
          (transportedEnergyThresholdDual R hR zMinus hzMinus)
          (bubbleRadialEnergyL2 R hR) v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  have hPlusC1 :
      ContDiffAt ℝ 1
        (transportedEnergyThresholdDual R hR zPlus hzPlus) 0 :=
    transportedEnergyThresholdDual_contDiffAt_zero
      R hR zPlus hzPlus
  have hMinusC1 :
      ContDiffAt ℝ 1
        (transportedEnergyThresholdDual R hR zMinus hzMinus) 0 :=
    transportedEnergyThresholdDual_contDiffAt_zero
      R hR zMinus hzMinus
  have hScale :
      HasDerivAt
        (fun a : ℝ =>
          transportedEnergyThresholdDual R hR zPlus hzPlus a
            (bubbleRadialEnergyL2 R hR))
        (-1) 0 := by
    simpa [bubbleRadialEnergyL2] using
      transportedEnergyThresholdDual_bubble_hasDerivAt
        R hR zPlus hzPlus hzPlusR hPlusNorm
  have hPhase :
      transportedEnergyThresholdDual R hR zMinus hzMinus 0
        (bubbleRadialEnergyL2 R hR) = 1 := by
    simpa [bubbleRadialEnergyL2] using
      transportedEnergyThresholdDual_bubble_zero_eq_one
        R hR zMinus hzMinus hMinusNorm
  exact scalePhase_local_modulation_physical
    (transportedEnergyThresholdDual R hR zPlus hzPlus)
    (transportedEnergyThresholdDual R hR zMinus hzMinus)
    (bubbleRadialEnergyL2 R hR)
    hPlusC1 hMinusC1 hScale hPhase

end HBL.Modulation
