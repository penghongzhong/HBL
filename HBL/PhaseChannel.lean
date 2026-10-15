import HBL.ModulationSliceJacobians
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp

/-!
The phase half of the first manuscript modulation Jacobian.

The manuscript treats the real and imaginary channels separately.  This
module verifies that the tested phase rotation is jointly C1 in the two
real state components and the phase parameter, and that its phase
derivative at a real normalized bubble is exactly (0,-1).
-/

noncomputable section

open scoped ContDiff Topology

namespace HBL.Modulation

section PhaseChannels

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Real and imaginary test channels after multiplication by exp(-i gamma).
The state is represented by its ordered real and imaginary parts. -/
def phaseChannelTest (ellPlus ellMinus : V →L[ℝ] ℝ)
    (u : V × V) (gamma : ℝ) : Param :=
  (Real.cos gamma * ellPlus u.1 + Real.sin gamma * ellPlus u.2,
    -Real.sin gamma * ellMinus u.1 + Real.cos gamma * ellMinus u.2)

/-- The phase-tested constraints are jointly C1 in the state and phase. -/
theorem phaseChannelTest_contDiffAt
    (ellPlus ellMinus : V →L[ℝ] ℝ)
    (u₀ : V × V) (gamma₀ : ℝ) :
    ContDiffAt ℝ 1
      (fun v : (V × V) × ℝ => phaseChannelTest ellPlus ellMinus v.1 v.2)
      (u₀, gamma₀) := by
  unfold phaseChannelTest
  fun_prop

/-- For a purely real state, the two phase channels decouple. -/
theorem phaseChannelTest_real_state
    (ellPlus ellMinus : V →L[ℝ] ℝ) (w : V) (gamma : ℝ) :
    phaseChannelTest ellPlus ellMinus (w, 0) gamma =
      (Real.cos gamma * ellPlus w, -Real.sin gamma * ellMinus w) := by
  simp [phaseChannelTest]

/-- The exact second column of the manuscript's normalized Jacobian. -/
theorem phaseChannelTest_hasDerivAt_real_state
    (ellPlus ellMinus : V →L[ℝ] ℝ) (w : V)
    (hMinus : ellMinus w = 1) :
    HasDerivAt
      (fun gamma : ℝ => phaseChannelTest ellPlus ellMinus (w, 0) gamma)
      (0, -1) 0 := by
  have hp :
      HasDerivAt (fun gamma : ℝ => Real.cos gamma * ellPlus w) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).mul_const (ellPlus w)
  have hm :
      HasDerivAt (fun gamma : ℝ => -Real.sin gamma * ellMinus w) (-1) 0 := by
    simpa [hMinus] using (Real.hasDerivAt_sin 0).neg.mul_const (ellMinus w)
  have hPair := hp.prodMk hm
  convert hPair using 1
  · funext gamma
    exact phaseChannelTest_real_state ellPlus ellMinus w gamma

end PhaseChannels

end HBL.Modulation
