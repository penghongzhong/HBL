import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Shell-sized Hartree nonlocal source: necessary time-iteration power budget

This module checks the exact exponent arithmetic for the shell-sensitive
Riesz remainder. If e(s) is of order s^(-9/8) and a physical shell can
reach X(s) of order s^(1/2), then e(s)^2 X(s)^(3/4)
has power -15/8. A time interval of length comparable to s loses one
power, giving -7/8 instead of the proposed correction scale -9/8.
This is a NEGATIVE diagnostic for a noncancelling, unweighted Duhamel
argument, not a claim about the actual Hartree PDE or an assumed rate.

The normalized time-evolution may have additional oscillatory, kernel,
or modulation cancellation; none is ruled out by these exact identities.
No original theorem-environment acceptance is claimed.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

/-- Multiplication by one physical s-sized time width consumes one
power of time decay in the shell-source estimate. -/
theorem actual_Hartree_shell_source_one_time_width
    (s : ℝ) (hs : 0 < s) :
    s * s ^ (-(15 / 8 : ℝ)) = s ^ (-(7 / 8 : ℝ)) := by
  calc
    s * s ^ (-(15 / 8 : ℝ)) =
        s ^ (1 : ℝ) * s ^ (-(15 / 8 : ℝ)) := by
          rw [Real.rpow_one]
    _ = s ^ ((1 : ℝ) + (-(15 / 8 : ℝ))) :=
          (Real.rpow_add hs _ _).symm
    _ = s ^ (-(7 / 8 : ℝ)) := by
          congr 1
          norm_num

/-- The time-accumulated exponent is worse than the desired first-layer
scale by an unbounded factor s^(1/4), rather than better by s^(-3/4). -/
theorem actual_Hartree_shell_accumulation_relative_factor
    (s : ℝ) (hs : 0 < s) :
    s ^ (-(7 / 8 : ℝ)) =
      s ^ (1 / 4 : ℝ) * s ^ (-(9 / 8 : ℝ)) := by
  calc
    s ^ (-(7 / 8 : ℝ)) =
        s ^ ((1 / 4 : ℝ) + (-(9 / 8 : ℝ))) := by
          congr 1
          norm_num
    _ = s ^ (1 / 4 : ℝ) * s ^ (-(9 / 8 : ℝ)) :=
          Real.rpow_add hs _ _

/-- With amplitude exponent 9/8 and shell growth exponent alpha,
a non-oscillatory time integration can preserve the first-profile
amplitude only for alpha at most 1/6. This is a necessary condition
for that particular method, not an estimate of the true moving shell. -/
theorem actual_Hartree_shell_plain_Duhamel_growth_threshold
    (alpha : ℝ)
    (hIteration : (2 : ℝ) * (9 / 8) - (3 / 4) * alpha ≥
       (9 / 8 : ℝ) + 1) :
    alpha ≤ (1 / 6 : ℝ) := by
  linarith

/-- If the actual shell grows as s^(1/2), then a bare time primitive
requires amplitude exponent at least 11/8 to retain its own order. -/
theorem actual_Hartree_shell_plain_Duhamel_amplitude_threshold
    (rho : ℝ)
    (hIteration : (2 : ℝ) * rho - (3 / 4) * (1 / 2 : ℝ) ≥
       rho + 1) :
    (11 / 8 : ℝ) ≤ rho := by
  linarith

end HBL.TypeIIDynamicSelection
