import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszSpatialDecay
import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import Mathlib.Tactic

/-!
# HBL revised 2.13: global inverse-radius decay of the actual moving-core Hartree potential

The genuine moving-cutoff monopole satisfies
  (1+r)|V_c(r)| <= D,   D=2+9*C_mon, |c|<=1.
Thus |V_c|^4 <= D^4 W^2. Positivity of the ORIGINAL 3D inverse-square
radial Hartree kernel and the independently certified scalar Riesz estimate
I[W^2](r) <= C/(1+r) imply
  |I[V_c^4](r)| <= D^4 C/(1+r),  r>0.

This improves the already checked uniform O(ell) core-potential Taylor
error for remote weighted source estimates. Unlike that error, the present
bound retains the physical far-field decay. The actual finite-profile
matching and Type-II dynamical rate remain open.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original full nonlocal Hartree potential of the moment-cutoff
monopole has a global inverse-radius tail, uniformly for |c|<=1.
No radiation time rate, free Riesz source, or matching datum is assumed. -/
theorem actual_Hartree_moving_core_Riesz_global_inverse_radius
    (c r : ℝ) (hc : |c| ≤ 1) (hr : 0 < r) :
    |radialHartreePotential
      (fun rho => monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c rho ^ 4) r| ≤
      ((2 + 9 * monopoleRadialBoundConstant) ^ 4 *
        actualHartreeBubbleSquaredRieszDecayConstant) / (1 + r) := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  have hD : 0 ≤ D := by
    dsimp [D]
    have hMon := monopoleRadialBoundConstant_pos
    positivity
  have hVmeas : Measurable V := by
    dsimp [V]
    exact actual_Hartree_moving_monopole_measurable c
  have hEnvelope : ∀ rho : ℝ, 0 < rho →
      |V rho ^ 4| ≤ D ^ 4 * bubble rho ^ 2 := by
    intro rho hrho
    have hV : (1 + rho) * |V rho| ≤ D := by
      dsimp [V, D]
      exact actual_Hartree_moving_monopole_one_plus_radius_decay c rho hrho hc
    have hG2 : 1 + rho ^ 2 ≤ (1 + rho) ^ 2 := by
      nlinarith [hrho.le]
    have hG4 : (1 + rho) ^ 2 ≤ (1 + rho) ^ 4 := by
      have hOne : (1 : ℝ) ≤ (1 + rho) ^ 2 := by
        nlinarith [hrho.le]
      have hSquare : 0 ≤ (1 + rho) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hSquare (sub_nonneg.mpr hOne)]
    have hEnergy : (1 + rho ^ 2) * |V rho| ^ 4 ≤ D ^ 4 := by
      calc
        (1 + rho ^ 2) * |V rho| ^ 4 ≤
            (1 + rho) ^ 4 * |V rho| ^ 4 :=
          mul_le_mul_of_nonneg_right (hG2.trans hG4) (by positivity)
        _ = ((1 + rho) * |V rho|) ^ 4 := by ring
        _ ≤ D ^ 4 :=
          pow_le_pow_left₀ (by positivity) hV 4
    have hBubbleSq : bubble rho ^ 2 = (1 + rho ^ 2)⁻¹ := by
      unfold bubble
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    have hInv : |V rho| ^ 4 ≤ D ^ 4 / (1 + rho ^ 2) :=
      (le_div_iff₀ (by positivity : 0 < 1 + rho ^ 2)).2 (by
        simpa only [mul_comm] using hEnergy)
    rw [abs_pow, hBubbleSq]
    simpa only [div_eq_mul_inv] using hInv
  have hCmp := actual_Hartree_Riesz_relative_bubble_sq_domination
    (fun rho : ℝ => V rho ^ 4)
    (hVmeas.pow_const 4) (D ^ 4) hEnvelope r hr
  have hScalar := actual_Hartree_bubble_squared_Riesz_spatial_decay r hr
  change |radialHartreePotential (fun rho => V rho ^ 4) r| ≤
    (D ^ 4 * actualHartreeBubbleSquaredRieszDecayConstant) / (1 + r)
  calc
    |radialHartreePotential (fun rho => V rho ^ 4) r| ≤
        D ^ 4 * radialHartreePotential (fun rho => bubble rho ^ 2) r := hCmp
    _ ≤ D ^ 4 * (actualHartreeBubbleSquaredRieszDecayConstant / (1 + r)) :=
      mul_le_mul_of_nonneg_left hScalar (by positivity)
    _ = (D ^ 4 * actualHartreeBubbleSquaredRieszDecayConstant) / (1 + r) :=
      by ring

end HBL.TypeIIDynamicSelection
