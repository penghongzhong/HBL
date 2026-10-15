import HBL.ManuscriptModulationConstraint

/-!
Recentering the transported compact test family at an arbitrary logarithmic
scale a0.

The key algebraic identity is
  C_zeta(a0+b,r) = C_{zeta[a0]}(b,r),
where
  zeta[a0](r) = exp(3a0/2) zeta(exp(a0) r).
Hence all operator-norm C1 estimates already proved at scale zero transfer
without any new analytic argument to every finite a0.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace HBL.Modulation

/-- Test function recentered at logarithmic scale a0. -/
def recenteredThresholdTest
    (zeta : ℝ → ℝ) (a₀ r : ℝ) : ℝ :=
  Real.exp ((3 / 2 : ℝ) * a₀) * zeta (Real.exp a₀ * r)

/-- Smooth compact tests remain C1 after recentering. -/
theorem recenteredThresholdTest_contDiff
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a₀ : ℝ) :
    ContDiff ℝ 1 (recenteredThresholdTest zeta a₀) := by
  change ContDiff ℝ 1 (fun r : ℝ =>
    Real.exp ((3 / 2 : ℝ) * a₀) * zeta (Real.exp a₀ * r))
  fun_prop

/-- Exact coefficient identity after translating the logarithmic parameter. -/
theorem transportedEnergyCoefficient_recenter
    (zeta : ℝ → ℝ) (a₀ b r : ℝ) :
    transportedEnergyCoefficient zeta (a₀ + b) r =
      transportedEnergyCoefficient
        (recenteredThresholdTest zeta a₀) b r := by
  unfold transportedEnergyCoefficient recenteredThresholdTest
  rw [Real.exp_add, Real.exp_add]
  ring_nf
  congr 2
  · congr 1
    ring
  · congr 1
    ring

/-- The corrected Hilbert tail is exactly translated by the same recentering. -/
theorem transportedEnergyTail_recenter
    (R : ℝ) (zeta : ℝ → ℝ) (a₀ b s : ℝ) :
    transportedEnergyTail R zeta (a₀ + b) s =
      transportedEnergyTail R
        (recenteredThresholdTest zeta a₀) b s := by
  unfold transportedEnergyTail
  apply intervalIntegral.integral_congr
  intro r _
  exact transportedEnergyCoefficient_recenter zeta a₀ b r

/-- The L2 Riesz representers inherit the exact translation identity. -/
theorem transportedEnergyTailL2_recenter
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ b : ℝ) :
    transportedEnergyTailL2 R hR zeta hzeta (a₀ + b) =
      transportedEnergyTailL2 R hR
        (recenteredThresholdTest zeta a₀)
        (recenteredThresholdTest_contDiff zeta hzeta a₀) b := by
  apply Lp.ext
  filter_upwards [
    transportedEnergyTailL2_ae R hR zeta hzeta (a₀ + b),
    transportedEnergyTailL2_ae R hR
      (recenteredThresholdTest zeta a₀)
      (recenteredThresholdTest_contDiff zeta hzeta a₀) b
  ] with s h1 h2
  rw [h1, h2]
  exact transportedEnergyTail_recenter R zeta a₀ b s

/-- The actual threshold dual translates exactly in operator space. -/
theorem transportedEnergyThresholdDual_recenter
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ b : ℝ) :
    transportedEnergyThresholdDual R hR zeta hzeta (a₀ + b) =
      transportedEnergyThresholdDual R hR
        (recenteredThresholdTest zeta a₀)
        (recenteredThresholdTest_contDiff zeta hzeta a₀) b := by
  unfold transportedEnergyThresholdDual
  rw [transportedEnergyTailL2_recenter R hR zeta hzeta a₀ b]

/-- C1 operator-norm dependence of the finite-radius dual at every
logarithmic scale, obtained by translation from the already verified
zero-scale theorem. -/
theorem transportedEnergyThresholdDual_contDiffAt
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ : ℝ) :
    ContDiffAt ℝ 1
      (transportedEnergyThresholdDual R hR zeta hzeta) a₀ := by
  let z₀ : ℝ → ℝ := recenteredThresholdTest zeta a₀
  have hz₀ : ContDiff ℝ 1 z₀ :=
    recenteredThresholdTest_contDiff zeta hzeta a₀
  have hzero :
      ContDiffAt ℝ 1
        (transportedEnergyThresholdDual R hR z₀ hz₀) 0 :=
    transportedEnergyThresholdDual_contDiffAt_zero R hR z₀ hz₀
  have hsub :
      ContDiffAt ℝ 1 (fun a : ℝ => a - a₀) a₀ := by
    fun_prop
  have hcomp :=
    hzero.comp a₀ hsub
  have heq :
      (fun a : ℝ =>
        transportedEnergyThresholdDual R hR z₀ hz₀ (a - a₀)) =
      transportedEnergyThresholdDual R hR zeta hzeta := by
    funext a
    have hadd : a = a₀ + (a - a₀) := by ring
    conv_rhs => rw [hadd]
    exact (transportedEnergyThresholdDual_recenter
      R hR zeta hzeta a₀ (a - a₀)).symm
  rw [heq] at hcomp
  exact hcomp

/-- The full half-line dual is C1 in operator norm at every logarithmic
scale as well. -/
theorem fullTransportedEnergyThresholdDual_contDiffAt
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta)
    (a₀ : ℝ) :
    ContDiffAt ℝ 1
      (fullTransportedEnergyThresholdDual R hR zeta hzeta) a₀ := by
  let P : FullRadialEnergyL2 →L[ℝ] RadialEnergyL2 R :=
    fullToFiniteRadialEnergy R
  let L :
      (RadialEnergyL2 R →L[ℝ] ℝ) →L[ℝ]
        (FullRadialEnergyL2 →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL
      ℝ FullRadialEnergyL2 (RadialEnergyL2 R) ℝ).flip P
  have hfinite :=
    transportedEnergyThresholdDual_contDiffAt
      R hR zeta hzeta a₀
  have hcomp := L.contDiff.contDiffAt.comp a₀ hfinite
  change ContDiffAt ℝ 1
    (fun a : ℝ =>
      (transportedEnergyThresholdDual R hR zeta hzeta a).comp
        (fullToFiniteRadialEnergy R)) a₀
  simpa [L, P, Function.comp_def] using hcomp

end HBL.Modulation
