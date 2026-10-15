import HBL.ModulationLemmaCertified
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
Phase quotient for the first manuscript modulation lemma.

The manuscript's phase parameter lives in R/(2*pi Z).  The implicit-function
argument is necessarily written in a real local lift.  This module verifies
that the tested residual is exactly invariant under changing that real lift
by an integral multiple of 2*pi, and records the corresponding Real.Angle
class.  Thus the verified local real selector canonically determines the
manuscript's quotient-valued phase.
-/

noncomputable section

open Real
open scoped Topology

namespace HBL.Modulation

/-- The phase class used in the manuscript: R/(2*pi Z). -/
def phaseClass (gamma : ℝ) : Real.Angle :=
  (gamma : Real.Angle)

/-- Changing a real phase representative by 2*pi*n does not change its
quotient phase. -/
theorem phaseClass_add_int_two_pi (gamma : ℝ) (n : ℤ) :
    phaseClass (gamma + (n : ℝ) * (2 * Real.pi)) =
      phaseClass gamma := by
  unfold phaseClass
  apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.2
  refine ⟨n, ?_⟩
  ring

section PeriodicResidual

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The scale-phase observable only depends on the phase modulo 2*pi. -/
theorem scalePhaseObservable_phase_add_int_two_pi
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ))
    (u : V × V) (a gamma : ℝ) (n : ℤ) :
    scalePhaseObservable Splus Sminus
        (u, (a, gamma + (n : ℝ) * (2 * Real.pi))) =
      scalePhaseObservable Splus Sminus (u, (a, gamma)) := by
  unfold scalePhaseObservable
  simp

/-- Therefore the normalized residual used by the IFT also depends on phase
only modulo 2*pi. -/
theorem scalePhaseResidual_phase_add_int_two_pi
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ))
    (w : V) (u : V × V) (a gamma : ℝ) (n : ℤ) :
    scalePhaseResidual Splus Sminus w
        (u, (a, gamma + (n : ℝ) * (2 * Real.pi))) =
      scalePhaseResidual Splus Sminus w
        (u, (a, gamma)) := by
  unfold scalePhaseResidual
  rw [scalePhaseObservable_phase_add_int_two_pi]

end PeriodicResidual

/-- The arbitrary-bubble absolute residual is invariant under replacing the
physical phase by any other representative of the same Real.Angle class. -/
theorem phasedAbsoluteResidual_phase_add_int_two_pi
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (a₀ gamma₀ : ℝ)
    (u : ComplexRadialDotH1)
    (lambda gamma : ℝ) (n : ℤ) :
    phasedAbsoluteResidual
        R₀ hR₀ zPlus zMinus hzPlus hzMinus a₀ gamma₀
        u (lambda, gamma + (n : ℝ) * (2 * Real.pi)) =
      phasedAbsoluteResidual
        R₀ hR₀ zPlus zMinus hzPlus hzMinus a₀ gamma₀
        u (lambda, gamma) := by
  unfold phasedAbsoluteResidual
  unfold absolutePhysicalToRelativeLog
  have hphase :
      gamma + (n : ℝ) * (2 * Real.pi) - gamma₀ =
        (gamma - gamma₀) + (n : ℝ) * (2 * Real.pi) := by
    ring
  rw [hphase]
  exact scalePhaseResidual_phase_add_int_two_pi
    _ _ _ _ (Real.log lambda - a₀) (gamma - gamma₀) n

end HBL.Modulation
