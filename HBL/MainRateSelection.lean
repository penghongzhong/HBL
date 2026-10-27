import HBL.KinematicPhysicalTimeAsymptotics
import Mathlib.Tactic

/-!
# Selected physical blow-up rate

The main theorem parametrizes the physical scale exponent by the terminal
modulation coordinate mu_infty.  This file records the elementary final
identification and its smooth dependence.
-/

noncomputable section
set_option autoImplicit false

open scoped Topology

namespace HBL.MainBackward

def selectedPhysicalRate (mu : ℝ) : ℝ := 2 * mu + 1 / 2

theorem selectedPhysicalRate_contDiff :
    ContDiff ℝ 1 selectedPhysicalRate := by
  unfold selectedPhysicalRate
  fun_prop

theorem selectedPhysicalRate_eq_two_iff (mu : ℝ) :
    selectedPhysicalRate mu = 2 ↔ mu = 3 / 4 := by
  unfold selectedPhysicalRate
  constructor <;> intro h <;> linarith

theorem selectedPhysicalRate_deriv :
    deriv selectedPhysicalRate = fun _ : ℝ => 2 := by
  funext mu
  have h : HasDerivAt selectedPhysicalRate 2 mu := by
    simpa [selectedPhysicalRate, mul_comm] using
      ((hasDerivAt_id mu).const_mul 2).add_const (1 / 2)
  exact h.deriv

#print axioms selectedPhysicalRate_contDiff
#print axioms selectedPhysicalRate_eq_two_iff
#print axioms selectedPhysicalRate_deriv

end HBL.MainBackward
