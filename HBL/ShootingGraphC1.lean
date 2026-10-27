import HBL.ParametricFixedPointC1
import HBL.WeightedBackwardPaths
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# C1 extraction of the shooting graph

Once the full parameter-dependent backward fixed point is C1, the unstable
initial coordinate is obtained by a continuous-linear projection followed by
evaluation at s0.  Thus no second parameter-differentiation argument for the
shooting integral is needed.
-/

noncomputable section
set_option autoImplicit false

open scoped Topology ContDiff

namespace HBL.MainBackward

abbrev UnstableWeightedPath (s0 : ℝ) :=
  BoundedContinuousFunction (LateTime s0) ℝ

/-- Evaluation at the initial late-time point. -/
def unstableInitialEvalCLM (s0 : ℝ) :
    UnstableWeightedPath s0 →L[ℝ] ℝ :=
  BoundedContinuousFunction.evalCLM ℝ
    (⟨s0, by simp [LateTime]⟩ : LateTime s0)

/-- Projection from a coupled centre/unstable state to the initial unstable
coordinate. -/
def shootingCoordinateCLM
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s0 : ℝ) :
    (X × UnstableWeightedPath s0) →L[ℝ] ℝ :=
  (unstableInitialEvalCLM s0).comp
    (ContinuousLinearMap.snd ℝ X (UnstableWeightedPath s0))

/-- A C1 coupled fixed-point graph has a C1 unstable shooting graph. -/
theorem shootingGraph_contDiffAt_of_stateGraph
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s0 : ℝ)
    (psi : P → X × UnstableWeightedPath s0)
    (p : P)
    (hpsi : ContDiffAt ℝ 1 psi p) :
    ContDiffAt ℝ 1
      (fun y => shootingCoordinateCLM (X := X) s0 (psi y)) p := by
  have houter :
      ContDiffAt ℝ 1 (shootingCoordinateCLM (X := X) s0) (psi p) :=
    (shootingCoordinateCLM (X := X) s0).contDiff.contDiffAt
  simpa only [Function.comp_def] using houter.comp p hpsi

#print axioms shootingGraph_contDiffAt_of_stateGraph

end HBL.MainBackward
