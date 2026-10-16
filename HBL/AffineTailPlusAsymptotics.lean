import HBL.AffineTailMinusFiniteGreen

/-!
Real-channel resonance: asymptotic constant and affine Green boundary data.

The scaling zero-mode identity below follows algebraically from the radial
conjugation identity; it uses the already checked H-minus resonance and does
not assume the (still pending) nonlocal equation H-plus psi-plus=0.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- Scaling and phase resonances obey an exact differential relation. -/
theorem resonancePlus_eq_radius_deriv_sub_half (r : ℝ) :
    resonancePlus r =
      r * deriv resonanceMinus r - resonanceMinus r / 2 := by
  have hb : ContDiff ℝ 1 bubble :=
    bubble_contDiff_infty.of_le (by norm_num)
  change r * dilationGenerator bubble r =
    r * deriv (radialU bubble) r - radialU bubble r / 2
  rw [radialU_deriv bubble hb r]
  unfold dilationGenerator radialU
  ring

/-- A consequence of the already verified imaginary-channel boundary limit. -/
theorem radius_resonanceMinus_deriv_tendsto_zero :
    Tendsto (fun R : ℝ => R * deriv resonanceMinus R)
      atTop (𝓝 (0 : ℝ)) := by
  have hsum :
      Tendsto
        (fun R : ℝ =>
          greenBoundary resonanceMinus (deriv resonanceMinus)
            model (deriv model) R + resonanceMinus R)
        atTop (𝓝 (0 : ℝ)) := by
    have h := greenBoundary_minus_tendsto_neg_one.add
      resonanceMinus_tendsto_one
    simpa using h
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with R hR
  rw [greenBoundary_minus_far R hR]
  have hd : deriv resonanceMinus R = bubbleRadialEnergyDerivative R := by
    change deriv (radialU bubble) R = bubbleRadialEnergyDerivative R
    exact radialU_bubble_deriv_closed R
  rw [hd]
  ring

/-- Explicit c-plus = -1/2, without re-differentiating a square-root quotient. -/
theorem resonancePlus_tendsto_neg_half :
    Tendsto resonancePlus atTop (𝓝 (-(1 / 2 : ℝ))) := by
  have hlim :
      Tendsto
        (fun R : ℝ =>
          R * deriv resonanceMinus R - resonanceMinus R / 2)
        atTop (𝓝 (-(1 / 2 : ℝ))) := by
    have h := radius_resonanceMinus_deriv_tendsto_zero.sub
      (resonanceMinus_tendsto_one.div_const 2)
    simpa using h
  exact hlim.congr' (Filter.Eventually.of_forall
    (fun R : ℝ => (resonancePlus_eq_radius_deriv_sub_half R).symm))

@[simp]
theorem resonancePlus_zero : resonancePlus 0 = 0 := by
  simp [resonancePlus, radialResonancePlus]

/-- The Dirichlet boundary term in the real channel vanishes at the origin. -/
theorem greenBoundary_plus_at_zero :
    greenBoundary resonancePlus (deriv resonancePlus)
      model (deriv model) 0 = 0 := by
  simp [greenBoundary]

/-- On the affine tail, the real-channel boundary is -psi-plus+R*psi-plus'. -/
theorem greenBoundary_plus_far (R : ℝ) (hR : 2 < R) :
    greenBoundary resonancePlus (deriv resonancePlus)
      model (deriv model) R =
      -resonancePlus R + R * deriv resonancePlus R := by
  unfold greenBoundary
  rw [model_eq_id_of_two_le R hR.le,
    model_deriv_eq_one_of_two_lt R hR]
  ring

end HBL.Modulation.AffineTail
