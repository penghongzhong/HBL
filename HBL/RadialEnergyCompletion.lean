import HBL.RadialEnergyIsometry
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
Smooth radial energy coordinates and completion of bounded tests.

The compact radial conjugation U(f)(r) = r*f(r) has derivative
f(r) + r*f'(r).  The fundamental theorem of calculus reconstructs U(f)
from this derivative, which is the variable used in the half-line Hilbert
realization of radial homogeneous energy.

Separately, every bounded linear test on an energy core extends uniquely
to its norm completion.  This is a theorem about an arbitrary normed core;
identifying the paper's concrete radial core and proving the scale-family
C1 estimate in its norm remain outstanding.
-/

noncomputable section

open MeasureTheory

namespace HBL.Modulation

/-- The radial conjugation is C1 whenever the profile is C1. -/
theorem radialU_contDiff_one (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (radialU f) := by
  change ContDiff ℝ 1 (fun r : ℝ => r * f r)
  exact contDiff_id.mul hf

/-- Fundamental theorem for the half-line radial energy coordinate.
The boundary term at the origin vanishes exactly, since U(f)(0)=0. -/
theorem radialU_integral_deriv (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (R : ℝ) :
    (∫ r in (0 : ℝ)..R, deriv (radialU f) r) = radialU f R := by
  have hU : ContDiff ℝ 1 (radialU f) := radialU_contDiff_one f hf
  have hD : Continuous (deriv (radialU f)) :=
    hU.continuous_deriv_one
  have hInt : IntervalIntegrable (deriv (radialU f)) volume 0 R :=
    hD.intervalIntegrable (μ := volume) (a := 0) (b := R)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => ((hU.differentiable (by norm_num) r).hasDerivAt)) hInt
  have hZero : radialU f 0 = 0 := by simp [radialU]
  simpa only [hZero, sub_zero] using hFTC

section CoreCompletion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous extension of a bounded test from a normed radial
energy core to its full norm completion. -/
def energyCoreTestExtension (ell : E →L[ℝ] ℝ) :
    UniformSpace.Completion E →L[ℝ] ℝ :=
  ell.fromCompletion

/-- The extension agrees exactly with the original core functional. -/
theorem energyCoreTestExtension_apply
    (ell : E →L[ℝ] ℝ) (v : E) :
    energyCoreTestExtension ell (v : UniformSpace.Completion E) = ell v := by
  exact ContinuousLinearMap.fromCompletion_apply_coe ell v

/-- A continuous functional on the completion is determined by its
values on the original dense energy core. -/
theorem energyCoreTestExtension_unique
    (ell : E →L[ℝ] ℝ)
    (L : UniformSpace.Completion E →L[ℝ] ℝ)
    (h : ∀ v : E, L (v : UniformSpace.Completion E) = ell v) :
    L = energyCoreTestExtension ell := by
  exact (ContinuousLinearMap.fromCompletion_unique ell L
    (fun v => (h v).symm)).symm

end CoreCompletion

end HBL.Modulation
