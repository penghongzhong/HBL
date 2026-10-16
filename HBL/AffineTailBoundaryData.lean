import HBL.AffineTailMinusZeroMode

/-!
Boundary data for the affine-tail Green formula in the H_- channel.

The chosen affine model is identically r for r>2, so its derivative is
exactly one there.  At the origin both the Dirichlet resonance and the
affine model vanish.  These facts reduce the Wronskian boundary term to
  -psi_-(R) + R psi_-'(R)
for all R>2.
-/

noncomputable section

open Filter

namespace HBL.Modulation.AffineTail

/-- The affine model has derivative one in the far field. -/
theorem model_hasDerivAt_one_of_two_lt
    (r : ℝ) (hr : 2 < r) :
    HasDerivAt model 1 r := by
  apply (hasDerivAt_id r).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hr] with x hx
  simpa only [id_eq] using model_eq_id_of_two_le x hx.le

theorem model_deriv_eq_one_of_two_lt
    (r : ℝ) (hr : 2 < r) :
    deriv model r = 1 :=
  (model_hasDerivAt_one_of_two_lt r hr).deriv

@[simp]
theorem model_zero :
    model 0 = 0 :=
  model_zero_of_le_one 0 (by norm_num)

@[simp]
theorem resonanceMinus_zero :
    resonanceMinus 0 = 0 := by
  simp [resonanceMinus, radialResonanceMinus, bubble]

/-- The Green boundary contribution at the origin vanishes identically. -/
theorem greenBoundary_minus_at_zero :
    greenBoundary resonanceMinus (deriv resonanceMinus)
      model (deriv model) 0 = 0 := by
  simp [greenBoundary]

/-- Exact far-field Wronskian formula for the phase resonance. -/
theorem greenBoundary_minus_far
    (R : ℝ) (hR : 2 < R) :
    greenBoundary resonanceMinus (deriv resonanceMinus)
      model (deriv model) R =
      -resonanceMinus R + bubbleRadialEnergyDerivative R * R := by
  unfold greenBoundary
  rw [model_eq_id_of_two_le R hR.le,
    model_deriv_eq_one_of_two_lt R hR]
  have hfirst :
      deriv resonanceMinus R = bubbleRadialEnergyDerivative R := by
    change deriv (radialU bubble) R = bubbleRadialEnergyDerivative R
    exact radialU_bubble_deriv_closed R
  rw [hfirst]
  ring

end HBL.Modulation.AffineTail
