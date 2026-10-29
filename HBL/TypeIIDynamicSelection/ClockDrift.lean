import HBL.TypeIIDynamicSelection.ClockIdentities

/-!
# Exact drift identity for the *actual* rescaled modulation coordinate

A successful physical Hartree projection must estimate this derivative.
The term b_s q + 4 b mu must be controlled together, including the
retained Hamiltonian threshold feedback: bounding b_s alone may be
insufficient because neither summand is assumed integrable separately.

This is an exact real-analysis identity for an arbitrary differentiated
scale path, not a proof that any Hartree solution exists.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Exact drift formula implied by the time, scale and b differential
identities, with no limit exponent, source decay or rate inserted as input. -/
theorem dynamicalMu_hasDerivAt
    (tau lambda b : ℝ → ℝ) (s bs : ℝ)
    (htau : HasDerivAt tau (-(lambda s)⁻¹ ^ 2) s)
    (hlambda : HasDerivAt lambda (b s * lambda s) s)
    (hln : lambda s ≠ 0)
    (hb : HasDerivAt b bs s) :
    HasDerivAt (dynamicalMu tau lambda b)
      ((bs * dynamicalClock tau lambda s +
          4 * b s * dynamicalMu tau lambda b s) / 2) s := by
  have hq := dynamicalClock_hasDerivAt tau lambda b s htau hlambda hln
  have hp := hb.mul hq
  convert ((hp.const_mul (2 : ℝ)).sub_const 1).div_const 4 using 1
  · funext t
    simp only [Pi.mul_apply]
    unfold dynamicalMu
    ring
  · ring

end HBL.TypeIIDynamicSelection
