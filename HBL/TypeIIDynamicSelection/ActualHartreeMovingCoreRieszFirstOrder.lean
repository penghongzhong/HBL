import HBL.MonopoleHartreeExpansion
import HBL.RadialHartreeBubbleExact
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# HBL 2.13 LEAP: original moving monopole quartic Riesz potential is
# the exact bubble Riesz potential plus a positive physical-moment defect

Instead of computing a new convolution of bubble^2, reuse the
previously proved FULL actual Hartree quartic Taylor expansion
and the EXACT radial inverse-square Riesz potential of bubble^4:
  I[bubble^4](r) = 3 bubble(r)^2.

For the TRUE moving-cutoff monopole V_c:
  |I[V_c^4](r) - 3 bubble(r)^2|
    <= 4 |c| C_row C_mon + C_remainder c^2.

The last two constants are already derived by actual physical Riesz
integrals and Fredholm monopole bounds. No new inverse, source
hypothesis, prescribed type-II rate, added axiom, or sorry is used.
When c=kappa_H ell m(z(t)), bounded physical moment implies
the error has genuine O(ell) gain independent of the unknown rate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- True physical cutoff Hartree core potential is an explicit
fixed bubble potential plus a fully controlled genuine Riesz
Taylor error. Holds also for zero monopole amplitude. -/
theorem actual_Hartree_moving_monopole_core_Riesz_first_order
    (c r : ℝ) (hc : |c| ≤ 1) (hr : 0 < r) :
    |radialHartreePotential
        (fun rho => monopolePerturbedRadialProfile
          (monopoleQuadraticRadius c) c rho ^ 4) r -
        3 * bubble r ^ 2| ≤
      4 * |c| * (radialHartreeRowBoundConstant *
        monopoleRadialBoundConstant) +
      monopoleHartreePotentialBoundConstant * c ^ 2 := by
  by_cases hc0 : c = 0
  · subst c
    have hSource :
        (fun rho => monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (0 : ℝ)) 0 rho ^ 4) =
        (fun rho => bubble rho ^ 4) := by
      funext rho
      simp [monopolePerturbedRadialProfile]
    rw [hSource, radialHartreePotential_bubble_four hr]
    norm_num
  · have hcPos : 0 < |c| := abs_pos.mpr hc0
    have hExpansion :=
      (monopoleHartreePotential_actual_expansion hcPos hc hr).2
    have hBubble := radialHartreePotential_bubble_four hr
    have hLinear :=
      (monopoleHartreeBaseLinear_control
        (R := monopoleQuadraticRadius c) hr).2.2
    have hRemainder :=
      (monopoleHartreeDensityPotential_quadratic_control
        hcPos hc hr).2
    let P : ℝ := radialHartreePotential
      (fun rho => bubble rho ^ 3 *
        monopoleInnerRadialProfile (monopoleQuadraticRadius c) rho) r
    let E : ℝ := radialHartreePotential
      (monopoleHartreeDensityRemainder (monopoleQuadraticRadius c) c) r
    have hExact :
        radialHartreePotential
            (fun rho => monopolePerturbedRadialProfile
              (monopoleQuadraticRadius c) c rho ^ 4) r -
          3 * bubble r ^ 2 =
        4 * c * P + E := by
      rw [hExpansion, hBubble]
      dsimp [P, E]
      ring
    rw [hExact]
    calc
      |4 * c * P + E| ≤ |4 * c * P| + |E| :=
        abs_add_le _ _
      _ = 4 * |c| * |P| + |E| := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        ring
      _ ≤ 4 * |c| * (radialHartreeRowBoundConstant *
          monopoleRadialBoundConstant) +
          monopoleHartreePotentialBoundConstant * c ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hLinear (by positivity))
          hRemainder

end HBL.TypeIIDynamicSelection
