import HBL.TransportedEnergyTailL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
Correct transported threshold functionals on the radial energy Hilbert space.

The corrected L2 representer Q_a is converted by the real Riesz map into
a genuine continuous linear functional.  This module proves:
* at a=0 it is exactly the original threshold functional;
* its operator-valued derivative follows from the strong L2 derivative;
* on every smooth radial core profile its value is exactly the original
  transported scalar testing integral;
* therefore the manuscript's bubble normalizations give the scale entry -1
  and the phase normalization 1 without any abstract Jacobian hypothesis.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace

namespace HBL.Modulation

/-- At zero logarithmic scale, the corrected transported L2 representer
is exactly the original compact-test Riesz vector. -/
theorem transportedEnergyTailL2_zero_eq_testTailPrimitiveL2
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    transportedEnergyTailL2 R hR zeta hzeta 0 =
      testTailPrimitiveL2 R hR zeta hzeta.continuous := by
  apply Lp.ext
  filter_upwards [
    transportedEnergyTailL2_ae R hR zeta hzeta 0,
    testTailPrimitiveL2_ae R hR zeta hzeta.continuous
  ] with s hs ht
  rw [hs, ht]
  exact transportedEnergyTail_zero R zeta s

/-- The corrected transported compact test as a continuous linear
functional on the concrete radial energy Hilbert space. -/
def transportedEnergyThresholdDual
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    RadialEnergyL2 R →L[ℝ] ℝ :=
  innerSL ℝ (transportedEnergyTailL2 R hR zeta hzeta a)

/-- At scale zero this is precisely the original threshold dual. -/
theorem transportedEnergyThresholdDual_zero
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    transportedEnergyThresholdDual R hR zeta hzeta 0 =
      energyThresholdDual R hR zeta hzeta.continuous := by
  unfold transportedEnergyThresholdDual energyThresholdDual
  rw [transportedEnergyTailL2_zero_eq_testTailPrimitiveL2
    R hR zeta hzeta]

/-- Strong L2 differentiation passes through the real Riesz isometry,
giving an operator-norm derivative of the actual test functional. -/
theorem transportedEnergyThresholdDual_hasDerivAt_zero
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    HasDerivAt
      (transportedEnergyThresholdDual R hR zeta hzeta)
      (innerSL ℝ
        (transportedEnergyTailScaleDerivativeL2
          R hR zeta hzeta 0)) 0 := by
  let V := RadialEnergyL2 R
  let L : V →L[ℝ] (V →L[ℝ] ℝ) :=
    (InnerProductSpace.toDualMap ℝ V).toContinuousLinearMap
  have hQ :=
    transportedEnergyTailL2_hasDerivAt_zero R hR zeta hzeta
  have hcomp :
      HasDerivAt
        (L ∘ transportedEnergyTailL2 R hR zeta hzeta)
        (L (transportedEnergyTailScaleDerivativeL2
          R hR zeta hzeta 0)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hQ
  change HasDerivAt
    (fun a : ℝ => innerSL ℝ
      (transportedEnergyTailL2 R hR zeta hzeta a))
    (innerSL ℝ
      (transportedEnergyTailScaleDerivativeL2 R hR zeta hzeta 0)) 0
  simpa [L, V, Function.comp_def] using hcomp

/-- On a smooth radial profile, the corrected Hilbert functional is
exactly the manuscript's transported scalar threshold test. -/
theorem transportedEnergyThresholdDual_on_radialCore
    (R : ℝ) (hR : 0 ≤ R)
    (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (hf : ContDiff ℝ 1 f)
    (a : ℝ) :
    transportedEnergyThresholdDual R hR zeta hzeta a
        (radialUDerivativeL2 R hR f hf) =
      transportedRadialTestIntegral R zeta f a := by
  let mu : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  have hQ := transportedEnergyTailL2_ae R hR zeta hzeta a
  have hg := radialUDerivativeL2_ae R hR f hf
  calc
    transportedEnergyThresholdDual R hR zeta hzeta a
        (radialUDerivativeL2 R hR f hf) =
        inner ℝ (transportedEnergyTailL2 R hR zeta hzeta a)
          (radialUDerivativeL2 R hR f hf) := by
            rfl
    _ = (∫ s, transportedEnergyTail R zeta a s *
          deriv (radialU f) s ∂mu) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hQ, hg] with s hsQ hsg
      rw [hsQ, hsg]
      simp [RCLike.inner_apply, mul_comm]
    _ = (∫ s in (0 : ℝ)..R,
          transportedEnergyTail R zeta a s *
            deriv (radialU f) s) := by
      rw [intervalIntegral.integral_of_le hR]
    _ = transportedRadialTestIntegral R zeta f a :=
      transportedEnergyTail_pairing_eq_testIntegral
        R zeta f hzeta hf a

/-- The positive-channel bubble normalization produces exactly the
scale Jacobian entry -1 for the actual Hilbert-space test family. -/
theorem transportedEnergyThresholdDual_bubble_hasDerivAt
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hzetaR : zeta R = 0)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonancePlus r) = 1) :
    HasDerivAt
      (fun a : ℝ =>
        transportedEnergyThresholdDual R hR zeta hzeta a
          (radialUDerivativeL2 R hR bubble bubble_contDiff))
      (-1) 0 := by
  have hscalar :=
    bubble_normalized_scale_integral
      R hR zeta hzeta hzetaR hNorm
  have heq :
      (fun a : ℝ =>
        transportedEnergyThresholdDual R hR zeta hzeta a
          (radialUDerivativeL2 R hR bubble bubble_contDiff)) =
      transportedRadialTestIntegral R zeta bubble := by
    funext a
    exact transportedEnergyThresholdDual_on_radialCore
      R hR zeta bubble hzeta bubble_contDiff a
  rw [heq]
  exact hscalar

/-- The negative-channel normalization gives value one at the bubble,
which is the phase-column normalization used in the first lemma. -/
theorem transportedEnergyThresholdDual_bubble_zero_eq_one
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonanceMinus r) = 1) :
    transportedEnergyThresholdDual R hR zeta hzeta 0
      (radialUDerivativeL2 R hR bubble bubble_contDiff) = 1 := by
  rw [transportedEnergyThresholdDual_on_radialCore
    R hR zeta bubble hzeta bubble_contDiff 0]
  rw [bubble_phase_pairing_at_zero]
  exact hNorm

end HBL.Modulation
