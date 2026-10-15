import HBL.PhasedBubbleModulation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Exact conversion between relative modulation parameters and the manuscript's
absolute physical parameters.

Relative chart:
  rho > 0, delta in R.
Absolute manuscript parameters:
  lambda = exp(a0) * rho,
  gamma  = gamma0 + delta.
The implicit-function residual uses logarithmic scale, so we also define
the inverse local coordinate
  (lambda,gamma) |-> (log lambda - a0, gamma - gamma0).

For positive scales these two descriptions are exactly equivalent.
-/

noncomputable section

open scoped Topology ContDiff

namespace HBL.Modulation

/-- Relative positive scale and relative phase to absolute physical parameters. -/
def relativePhysicalToAbsolute
    (a₀ gamma₀ : ℝ) (p : Param) : Param :=
  (Real.exp a₀ * p.1, gamma₀ + p.2)

/-- Absolute physical parameters to relative logarithmic coordinates. -/
def absolutePhysicalToRelativeLog
    (a₀ gamma₀ : ℝ) (p : Param) : Param :=
  (Real.log p.1 - a₀, p.2 - gamma₀)

@[simp]
theorem relativePhysicalToAbsolute_base
    (a₀ gamma₀ : ℝ) :
    relativePhysicalToAbsolute a₀ gamma₀ (1, 0) =
      (Real.exp a₀, gamma₀) := by
  simp [relativePhysicalToAbsolute]

/-- Absolute scale produced from a positive relative scale is positive. -/
theorem relativePhysicalToAbsolute_scale_pos
    (a₀ gamma₀ : ℝ) (p : Param) (hp : 0 < p.1) :
    0 < (relativePhysicalToAbsolute a₀ gamma₀ p).1 := by
  simp only [relativePhysicalToAbsolute]
  exact mul_pos (Real.exp_pos a₀) hp

/-- Converting a relative physical parameter to absolute parameters and
then taking the relative logarithmic coordinate recovers (log rho,delta). -/
theorem absolutePhysicalToRelativeLog_relative
    (a₀ gamma₀ : ℝ) (p : Param) (hp : 0 < p.1) :
    absolutePhysicalToRelativeLog a₀ gamma₀
        (relativePhysicalToAbsolute a₀ gamma₀ p) =
      (Real.log p.1, p.2) := by
  apply Prod.ext
  · change Real.log (Real.exp a₀ * p.1) - a₀ = Real.log p.1
    rw [Real.log_mul (Real.exp_ne_zero a₀) hp.ne', Real.log_exp]
    ring
  · simp [absolutePhysicalToRelativeLog, relativePhysicalToAbsolute]

/-- Equality of relative log coordinates is exactly equality of positive
absolute physical parameters. This is the algebraic core of local uniqueness. -/
theorem relativeLog_eq_absoluteLog_iff
    (a₀ gamma₀ : ℝ) (q p : Param)
    (hq : 0 < q.1) (hp : 0 < p.1) :
    ((Real.log q.1, q.2) =
        absolutePhysicalToRelativeLog a₀ gamma₀ p) ↔
      relativePhysicalToAbsolute a₀ gamma₀ q = p := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext
    · change Real.exp a₀ * q.1 = p.1
      have hlog :
          a₀ + Real.log q.1 = Real.log p.1 := by
        change Real.log q.1 =
          Real.log p.1 - a₀ at h1
        linarith
      calc
        Real.exp a₀ * q.1 =
            Real.exp a₀ * Real.exp (Real.log q.1) := by
              rw [Real.exp_log hq]
        _ = Real.exp (a₀ + Real.log q.1) := by
              rw [Real.exp_add]
        _ = Real.exp (Real.log p.1) := by rw [hlog]
        _ = p.1 := Real.exp_log hp
    · change gamma₀ + q.2 = p.2
      change q.2 = p.2 - gamma₀ at h2
      linarith
  · intro h
    rw [← h]
    exact (absolutePhysicalToRelativeLog_relative
      a₀ gamma₀ q hq).symm

/-- The relative-to-absolute physical parameter map is C1 everywhere. -/
theorem relativePhysicalToAbsolute_contDiffAt
    (a₀ gamma₀ : ℝ) (p : Param) :
    ContDiffAt ℝ 1
      (relativePhysicalToAbsolute a₀ gamma₀) p := by
  change ContDiffAt ℝ 1
    (fun q : Param =>
      (Real.exp a₀ * q.1, gamma₀ + q.2)) p
  fun_prop

/-- The absolute-to-relative logarithmic coordinate is C1 at every
positive-scale point (indeed at every nonzero first coordinate). -/
theorem absolutePhysicalToRelativeLog_contDiffAt
    (a₀ gamma₀ : ℝ) (p : Param) (hp : p.1 ≠ 0) :
    ContDiffAt ℝ 1
      (absolutePhysicalToRelativeLog a₀ gamma₀) p := by
  have hfst :
      ContDiffAt ℝ 1 (fun q : Param => q.1) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff.contDiffAt
  have hsnd :
      ContDiffAt ℝ 1 (fun q : Param => q.2) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff.contDiffAt
  change ContDiffAt ℝ 1
    (fun q : Param =>
      (Real.log q.1 - a₀, q.2 - gamma₀)) p
  exact (hfst.log hp).sub contDiffAt_const |>.prodMk
    (hsnd.sub contDiffAt_const)

end HBL.Modulation
