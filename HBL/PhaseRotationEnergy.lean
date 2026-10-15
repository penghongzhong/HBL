import HBL.ScaledBubbleRadialEnergy
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Module

/-!
Fixed phase rotation on the complex radial dot-H1 energy model.

The complex state is represented by a pair of real radial energy coordinates.
Multiplication by exp(-i gamma) is therefore the bounded linear rotation
  (x,y) |-> (cos gamma x + sin gamma y,
             -sin gamma x + cos gamma y).
Its inverse is the rotation at -gamma.  This gives the exact topological
transport needed to move the standard phase-zero modulation chart to a
bubble with arbitrary fixed phase.
-/

noncomputable section

open scoped Topology

namespace HBL.Modulation

section PhaseRotation

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous linear phase rotation representing multiplication by exp(-i gamma). -/
def phaseRotationCLM (gamma : ℝ) : (E × E) →L[ℝ] (E × E) :=
  ((Real.cos gamma) • ContinuousLinearMap.fst ℝ E E +
      (Real.sin gamma) • ContinuousLinearMap.snd ℝ E E).prod
    ((-Real.sin gamma) • ContinuousLinearMap.fst ℝ E E +
      (Real.cos gamma) • ContinuousLinearMap.snd ℝ E E)

@[simp]
theorem phaseRotationCLM_apply (gamma : ℝ) (u : E × E) :
    phaseRotationCLM (E := E) gamma u =
      (Real.cos gamma • u.1 + Real.sin gamma • u.2,
       (-Real.sin gamma) • u.1 + Real.cos gamma • u.2) := by
  rfl

/-- Rotation by -gamma is a left inverse. -/
theorem phaseRotationCLM_neg_leftInverse (gamma : ℝ) :
    Function.LeftInverse
      (phaseRotationCLM (E := E) (-gamma))
      (phaseRotationCLM (E := E) gamma) := by
  intro u
  rcases u with ⟨x, y⟩
  ext <;>
    simp [phaseRotationCLM_apply, Real.cos_neg, Real.sin_neg] <;>
    module <;>
    nlinarith [Real.sin_sq_add_cos_sq gamma]

/-- Rotation by -gamma is also a right inverse. -/
theorem phaseRotationCLM_neg_rightInverse (gamma : ℝ) :
    Function.RightInverse
      (phaseRotationCLM (E := E) (-gamma))
      (phaseRotationCLM (E := E) gamma) := by
  intro u
  rcases u with ⟨x, y⟩
  ext <;>
    simp [phaseRotationCLM_apply, Real.cos_neg, Real.sin_neg] <;>
    module <;>
    nlinarith [Real.sin_sq_add_cos_sq gamma]

/-- Fixed phase rotation as a continuous linear equivalence. -/
def phaseRotationCLE (gamma : ℝ) : (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse
    (phaseRotationCLM (E := E) gamma)
    (phaseRotationCLM (E := E) (-gamma))
    (phaseRotationCLM_neg_leftInverse (E := E) gamma)
    (phaseRotationCLM_neg_rightInverse (E := E) gamma)

@[simp]
theorem phaseRotationCLE_apply (gamma : ℝ) (u : E × E) :
    phaseRotationCLE (E := E) gamma u =
      phaseRotationCLM (E := E) gamma u := by
  rfl

end PhaseRotation

/-- Energy-coordinate state of exp(i gamma0) W at logarithmic scale a0. -/
def phasedBubbleRadialDotH1
    (a₀ gamma₀ : ℝ) : ComplexRadialDotH1 :=
  (Real.cos gamma₀ • bubbleAtLogScaleRadialDotH1 a₀,
   Real.sin gamma₀ • bubbleAtLogScaleRadialDotH1 a₀)

/-- Multiplication by exp(-i gamma0) sends the phased bubble back to its
real positive representative. -/
theorem phaseRotationCLE_phasedBubble
    (a₀ gamma₀ : ℝ) :
    phaseRotationCLE (E := RadialDotH1) gamma₀
      (phasedBubbleRadialDotH1 a₀ gamma₀) =
      (bubbleAtLogScaleRadialDotH1 a₀, (0 : RadialDotH1)) := by
  let w : RadialDotH1 := bubbleAtLogScaleRadialDotH1 a₀
  change phaseRotationCLM (E := RadialDotH1) gamma₀
      (Real.cos gamma₀ • w, Real.sin gamma₀ • w) =
    (w, (0 : RadialDotH1))
  rw [phaseRotationCLM_apply]
  apply Prod.ext
  · change Real.cos gamma₀ • (Real.cos gamma₀ • w) +
        Real.sin gamma₀ • (Real.sin gamma₀ • w) = w
    rw [smul_smul, smul_smul, ← add_smul]
    have htrig :
        Real.cos gamma₀ * Real.cos gamma₀ +
          Real.sin gamma₀ * Real.sin gamma₀ = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq gamma₀]
    rw [htrig, one_smul]
  · change (-Real.sin gamma₀) • (Real.cos gamma₀ • w) +
        Real.cos gamma₀ • (Real.sin gamma₀ • w) = 0
    rw [smul_smul, smul_smul, ← add_smul]
    have hzero :
        (-Real.sin gamma₀) * Real.cos gamma₀ +
          Real.cos gamma₀ * Real.sin gamma₀ = 0 := by ring
    rw [hzero, zero_smul]

end HBL.Modulation
