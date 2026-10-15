import HBL.ConstraintJacobian
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
Regularity interface for the first manuscript lemma.

The scale action itself has an unbounded infinitesimal generator on the
homogeneous energy space, so the robust implicit-function argument tests the
scaled state first.  After moving the scale action onto the compactly
supported test functions, one only needs a C1 family of bounded dual maps.
This file formalizes that Banach-space step.
-/

noncomputable section

open scoped Topology ContDiff

namespace HBL.Modulation

section DualTestRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A parameter-dependent pair of bounded test functionals, evaluated on the
state variable and shifted by a fixed normalization vector. -/
def dualTestConstraint (B : Param → (E →L[ℝ] Param)) (c : Param)
    (v : E × Param) : Param :=
  B v.2 v.1 - c

/-- C1 regularity of the dual family is sufficient for joint C1 regularity of
the orthogonality constraints in state and parameters.  No differentiability
of the full scale action as an operator on the energy space is required. -/
theorem dualTestConstraint_contDiffAt
    (B : Param → (E →L[ℝ] Param)) (c : Param)
    (u₀ : E) (p₀ : Param)
    (hB : ContDiffAt ℝ 1 B p₀) :
    ContDiffAt ℝ 1 (dualTestConstraint B c) (u₀, p₀) := by
  have hBp :
      ContDiffAt ℝ 1 (fun v : E × Param => B v.2) (u₀, p₀) := by
    exact hB.comp (u₀, p₀)
      (ContinuousLinearMap.snd ℝ E Param).contDiff.contDiffAt
  have hu :
      ContDiffAt ℝ 1 (fun v : E × Param => v.1) (u₀, p₀) :=
    (ContinuousLinearMap.fst ℝ E Param).contDiff.contDiffAt
  have happ :
      ContDiffAt ℝ 1 (fun v : E × Param => B v.2 v.1) (u₀, p₀) :=
    hBp.clm_apply hu
  change ContDiffAt ℝ 1 (fun v : E × Param => B v.2 v.1 - c) (u₀, p₀)
  exact happ.sub contDiffAt_const

/-- The value of the dual constraint at the base point is zero exactly when
the normalization vector is the tested base state. -/
theorem dualTestConstraint_base_zero
    (B : Param → (E →L[ℝ] Param)) (u₀ : E) (p₀ : Param) :
    dualTestConstraint B (B p₀ u₀) (u₀, p₀) = 0 := by
  simp [dualTestConstraint]

end DualTestRegularity

end HBL.Modulation
