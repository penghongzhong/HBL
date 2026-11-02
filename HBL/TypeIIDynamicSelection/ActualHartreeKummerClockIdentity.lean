import HBL.TypeIIDynamicSelection.ActualHartreeKummerCoordinateBridge
import Mathlib.Tactic

/-!
# Original 2.12: the true terminal physical clock removes lambda from Kummer cutoff

The original physical variables satisfy the EXACT identities
  ell = lambda^{-1}, q = (T-t)*lambda^2 = (T-t)/ell^2.

Therefore, for ell>0 and T-t>0:
  ell*sqrt(q) = sqrt(T-t),
  R_K = 4/(kappa_H * m(t) * sqrt(T-t)).

This is NOT a Type-II rate statement. It proves that the physical
Kummer-coordinate cutoff's separation from any fixed normalized
Kummer annulus follows solely from terminal physical-time convergence
and a bounded positive Hartree radiation moment. No extra trapping
hypothesis beta>1/2 is required for this geometric step.

The genuine Hartree PDE, the modulation equations and finite-time
construction remain separate original obligations.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact cancellation of the concentration scale between
the physical clock and the Kummer self-similar radius.
No asymptotic expansion or prescribed concentration rate. -/
theorem actual_Hartree_Kummer_clock_sqrt_scale_exact
    (ell tau : ℝ) (hell : 0 < ell) (htau : 0 < tau) :
    ell * Real.sqrt (tau / ell ^ 2) = Real.sqrt tau := by
  have hq : 0 ≤ tau / ell ^ 2 := by positivity
  have hl : 0 ≤ ell * Real.sqrt (tau / ell ^ 2) := by positivity
  have hr : 0 ≤ Real.sqrt tau := Real.sqrt_nonneg _
  have hSq :
      (ell * Real.sqrt (tau / ell ^ 2)) ^ 2 =
        (Real.sqrt tau) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq, Real.sq_sqrt htau.le]
    field_simp [hell.ne']
  nlinarith [hSq]

/-- The *correctly transformed* Kummer cutoff is controlled only
by the remaining physical time and genuine Hartree quartic moment,
not by the unknown rate lambda(t) of the Type-II blowup. -/
theorem actual_Hartree_Kummer_cutoff_true_physical_clock
    (ell tau m : ℝ)
    (hell : 0 < ell) (htau : 0 < tau) (hm : 0 < m) :
    actualHartreeKummerCoordinateCutoffRadius ell
        (tau / ell ^ 2) m =
      4 / (hartreeKappa * m * Real.sqrt tau) := by
  have hScale := actual_Hartree_Kummer_clock_sqrt_scale_exact
    ell tau hell htau
  unfold actualHartreeKummerCoordinateCutoffRadius
    actualHartreeMomentCutoffRadius
  have hDen :
      hartreeKappa * (ell * Real.sqrt (tau / ell ^ 2)) * m =
        hartreeKappa * m * Real.sqrt tau := by
    rw [hScale]
    ring
  rw [hDen]

end HBL.TypeIIDynamicSelection
