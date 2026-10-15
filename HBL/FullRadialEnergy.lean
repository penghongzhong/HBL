import HBL.TailLiftedModulation
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Full half-line radial-energy model for the first modulation lemma.

The real radial homogeneous-energy coordinate is realized as
  L2((0,∞), dr)
for q = (r f(r))'.  A compact threshold test supported before R only
depends on the restriction of q to (0,R).  This file constructs the
canonical bounded restriction map from the full half-line L2 space to
the finite-radius model and lifts the corrected transported threshold
duals by precomposition.

The resulting modulation theorem is already a theorem on the full
half-line energy Hilbert space.  Its base point is any full vector whose
restriction equals the finite-radius stationary-bubble coordinate.
The last bubble-specific task is to construct the explicit full bubble
vector and verify this restriction identity.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Full one-dimensional radial homogeneous-energy coordinate. -/
abbrev FullRadialEnergyL2 : Type :=
  Lp ℝ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- The finite interval measure is dominated by the full half-line measure. -/
theorem finiteRadialMeasure_le_full (R : ℝ) :
    volume.restrict (Ioc (0 : ℝ) R) ≤
      volume.restrict (Ioi (0 : ℝ)) := by
  exact volume.restrict_mono_set (by
    intro r hr
    exact hr.1)

/-- Canonical bounded restriction from full half-line radial energy to
the finite interval (0,R). -/
def fullToFiniteRadialEnergy (R : ℝ) :
    FullRadialEnergyL2 →L[ℝ] RadialEnergyL2 R :=
  Lp.LpToLpOfMeasureLeSMul
    (E := ℝ) (p := 2)
    (μ := volume.restrict (Ioc (0 : ℝ) R))
    (ν := volume.restrict (Ioi (0 : ℝ)))
    (c := 1)
    (by simp)
    (by simpa using finiteRadialMeasure_le_full R)

/-- The restriction map agrees almost everywhere with the original full
L2 representative on (0,R). -/
theorem fullToFiniteRadialEnergy_ae
    (R : ℝ) (q : FullRadialEnergyL2) :
    (fullToFiniteRadialEnergy R q : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)] q := by
  unfold fullToFiniteRadialEnergy
  exact Lp.coeFn_LpToLpOfMeasureLeSMul
    (E := ℝ) (p := 2)
    (μ := volume.restrict (Ioc (0 : ℝ) R))
    (ν := volume.restrict (Ioi (0 : ℝ)))
    (c := 1)
    (by simp)
    (by simpa using finiteRadialMeasure_le_full R) q

/-- Correct transported compact threshold functional on the full
half-line radial-energy Hilbert space. -/
def fullTransportedEnergyThresholdDual
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a : ℝ) :
    FullRadialEnergyL2 →L[ℝ] ℝ :=
  (transportedEnergyThresholdDual R hR zeta hzeta a).comp
    (fullToFiniteRadialEnergy R)

@[simp]
theorem fullTransportedEnergyThresholdDual_apply
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a : ℝ) (q : FullRadialEnergyL2) :
    fullTransportedEnergyThresholdDual R hR zeta hzeta a q =
      transportedEnergyThresholdDual R hR zeta hzeta a
        (fullToFiniteRadialEnergy R q) := by
  rfl

/-- The actual transported full-space test family is C1 in operator norm. -/
theorem fullTransportedEnergyThresholdDual_contDiffAt_zero
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    ContDiffAt ℝ 1
      (fullTransportedEnergyThresholdDual R hR zeta hzeta) 0 := by
  let P : FullRadialEnergyL2 →L[ℝ] RadialEnergyL2 R :=
    fullToFiniteRadialEnergy R
  let L :
      (RadialEnergyL2 R →L[ℝ] ℝ) →L[ℝ]
        (FullRadialEnergyL2 →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL
      ℝ FullRadialEnergyL2 (RadialEnergyL2 R) ℝ).flip P
  have hfinite :=
    transportedEnergyThresholdDual_contDiffAt_zero
      R hR zeta hzeta
  have hcomp := L.contDiff.contDiffAt.comp 0 hfinite
  change ContDiffAt ℝ 1
    (fun a : ℝ =>
      (transportedEnergyThresholdDual R hR zeta hzeta a).comp
        (fullToFiniteRadialEnergy R)) 0
  simpa [L, P, Function.comp_def] using hcomp

/-- If a full radial-energy state restricts to the stationary-bubble
coordinate, the positive test has scale derivative -1. -/
theorem fullTransportedEnergyThresholdDual_bubble_hasDerivAt_of_restrict
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hzetaR : zeta R = 0)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonancePlus r) = 1)
    (w : FullRadialEnergyL2)
    (hw : fullToFiniteRadialEnergy R w =
      bubbleRadialEnergyL2 R hR) :
    HasDerivAt
      (fun a : ℝ =>
        fullTransportedEnergyThresholdDual
          R hR zeta hzeta a w)
      (-1) 0 := by
  have h :=
    transportedEnergyThresholdDual_bubble_hasDerivAt
      R hR zeta hzeta hzetaR hNorm
  have heq :
      (fun a : ℝ =>
        fullTransportedEnergyThresholdDual R hR zeta hzeta a w) =
      (fun a : ℝ =>
        transportedEnergyThresholdDual R hR zeta hzeta a
          (bubbleRadialEnergyL2 R hR)) := by
    funext a
    simp [fullTransportedEnergyThresholdDual, hw]
  rw [heq]
  exact h

/-- The negative-channel normalization remains one at any full state
whose finite restriction is the stationary bubble. -/
theorem fullTransportedEnergyThresholdDual_bubble_zero_eq_one_of_restrict
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonanceMinus r) = 1)
    (w : FullRadialEnergyL2)
    (hw : fullToFiniteRadialEnergy R w =
      bubbleRadialEnergyL2 R hR) :
    fullTransportedEnergyThresholdDual R hR zeta hzeta 0 w = 1 := by
  rw [fullTransportedEnergyThresholdDual_apply, hw]
  exact transportedEnergyThresholdDual_bubble_zero_eq_one
    R hR zeta hzeta hNorm

/-- Full-half-line modulation theorem, conditional only on identifying
the explicit bubble with a full L2 energy vector having the correct
finite restriction.  All compact-test and IFT regularity is already
fully discharged. -/
theorem fullRadialEnergy_local_modulation_of_restrict_bubble
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
        zMinus r * radialResonanceMinus r) = 1)
    (w : FullRadialEnergyL2)
    (hw : fullToFiniteRadialEnergy R w =
      bubbleRadialEnergyL2 R hR) :
    ∃ Phi : (FullRadialEnergyL2 × FullRadialEnergyL2) → Param,
      Phi (w, (0 : FullRadialEnergyL2)) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi (w, (0 : FullRadialEnergyL2)) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝 (w, (0 : FullRadialEnergyL2)),
        scalePhaseResidual
          (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
          (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
          w
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝
        ((w, (0 : FullRadialEnergyL2)), (0 : Param)),
        (scalePhaseResidual
          (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
          (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
          w v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  have hPlusC1 :=
    fullTransportedEnergyThresholdDual_contDiffAt_zero
      R hR zPlus hzPlus
  have hMinusC1 :=
    fullTransportedEnergyThresholdDual_contDiffAt_zero
      R hR zMinus hzMinus
  have hScale :=
    fullTransportedEnergyThresholdDual_bubble_hasDerivAt_of_restrict
      R hR zPlus hzPlus hzPlusR hPlusNorm w hw
  have hPhase :=
    fullTransportedEnergyThresholdDual_bubble_zero_eq_one_of_restrict
      R hR zMinus hzMinus hMinusNorm w hw
  exact scalePhase_local_modulation_physical
    (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
    (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
    w hPlusC1 hMinusC1 hScale hPhase

end HBL.Modulation
