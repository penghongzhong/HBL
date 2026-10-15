import HBL.PhysicalParameters
import HBL.ThresholdFunctionalBound
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Closure layer for the first manuscript lemma.

This file does two things:
1. records the standard passage from a norm-bounded linear functional to a
   continuous linear functional;
2. combines the already verified implicit-function step with the exponential
   change from logarithmic scale to the manuscript's physical parameter
   `lambda > 0`.

Thus the remaining analytic interface is isolated to the actual radial energy
realization and the C1 scale/phase residual.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation

section BoundedFunctional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear functional with a global norm bound is a continuous linear
functional.  This is the exact functional-analytic passage used after the
Hardy estimate for the manuscript's `ell_+` and `ell_-`. -/
def continuousFunctionalOfBound
    (L : E →ₗ[ℝ] ℝ) (C : ℝ)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) : E →L[ℝ] ℝ :=
  L.mkContinuous C h

@[simp]
theorem continuousFunctionalOfBound_apply
    (L : E →ₗ[ℝ] ℝ) (C : ℝ)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) (x : E) :
    continuousFunctionalOfBound L C h x = L x := by
  rfl

theorem continuousFunctionalOfBound_norm_le
    (L : E →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) :
    ‖continuousFunctionalOfBound L C h‖ ≤ C := by
  exact LinearMap.mkContinuous_norm_le L hC h

end BoundedFunctional

section PhysicalClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Physical-parameter version of the local modulation theorem.

The selector `Phi u = (lambda u, gamma u)` satisfies `lambda u > 0`;
the tested residual is evaluated at the corresponding logarithmic coordinate
`(log lambda, gamma)`.  The last clause is the local uniqueness statement. -/
theorem local_modulation_physical_from_tested_residual
    (ellPlus ellMinus : E →L[ℝ] ℝ) (w z : E)
    (R : E × Param → E) (u₀ : E)
    (hR0 : R (u₀, (0 : Param)) = 0)
    (hC1 : ContDiffAt ℝ 1 R (u₀, (0 : Param)))
    (hRparam :
      (fderiv ℝ R (u₀, (0 : Param))).comp
          (ContinuousLinearMap.inr ℝ E Param) =
        symmetryTangent w z)
    (hPlus : ellPlus z = 1) (hMinus : ellMinus w = 1)
    (hPlusCross : ellPlus w = 0) (hMinusCross : ellMinus z = 0) :
    ∃ Phi : E → Param,
      Phi u₀ = (1, 0) ∧
      ContDiffAt ℝ 1 Phi u₀ ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝 u₀,
        testedConstraint ellPlus ellMinus R
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝 (u₀, (0 : Param)),
        (testedConstraint ellPlus ellMinus R v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  obtain ⟨psi, hpsi0, hpsiC1, hsolve, huniq⟩ :=
    local_modulation_from_tested_residual
      ellPlus ellMinus w z R u₀ hR0 hC1 hRparam
      hPlus hMinus hPlusCross hMinusCross
  let Phi : E → Param := fun u => physicalParameters (psi u)
  have hPhi0 : Phi u₀ = (1, 0) := by
    simp [Phi, hpsi0]
  have hPhiC1 : ContDiffAt ℝ 1 Phi u₀ := by
    exact (physicalParameters_contDiffAt (psi u₀)).comp u₀ hpsiC1
  have hPhiPos : ∀ u, 0 < (Phi u).1 := by
    intro u
    exact physicalParameters_scale_pos (psi u)
  have hlog (u : E) :
      (Real.log (Phi u).1, (Phi u).2) = psi u := by
    exact log_physicalParameters_left_inverse (psi u)
  refine ⟨Phi, hPhi0, hPhiC1, hPhiPos, ?_, ?_⟩
  · filter_upwards [hsolve] with u hu
    rw [hlog u]
    exact hu
  · filter_upwards [huniq] with v hv
    rw [hlog v.1]
    exact hv

end PhysicalClosure

end HBL.Modulation
