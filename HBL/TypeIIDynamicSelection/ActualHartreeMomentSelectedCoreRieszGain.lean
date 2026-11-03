import HBL.TypeIIDynamicSelection.ActualHartreeMovingCoreRieszFirstOrder
import HBL.TypeIIDynamicSelection.ActualRadiation3DMoment
import Mathlib.Tactic

/-!
# Genuine Hartree moving core: O(ell) potential source for a bounded physical moment

The physical center is c=kappa_H*ell*m(t), with the full inverse-square
quartic moment m(t) of the regular radiation. For every positive moment
upper bound M, take a real scale 0<ell<=min(1, 1/(kappa_H*M)).
The core potential is the exact bubble potential plus an O(ell)
Taylor remainder. No time blowup exponent, free source coefficient or
fictitious Riesz kernel is introduced. Its proof reuses the already
strict-accepted physical monopole Hartree Taylor estimate.

To apply to a single Hartree PDE orbit, m(t) must be its genuine
radialPhysicalQuarticMoment(z(t)); its boundedness follows from the
separately certified physical moment continuity window. This theorem
does not close the other mixed/remote nonlinear source terms.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Physical quartic moment m bounds the true moving-core Riesz
source with a positive length order, not a prescribed time rate. -/
theorem actual_Hartree_moment_selected_core_Riesz_length_gain
    (ell m M r : ℝ)
    (hell : 0 < ell)
    (hM : 0 < M)
    (hm : 0 ≤ m) (hmM : m ≤ M)
    (hellMax : ell ≤ min 1 (1 / (hartreeKappa * M)))
    (hr : 0 < r) :
    let c := hartreeKappa * ell * m
    let K := hartreeKappa * M
    |radialHartreePotential
        (fun rho => monopolePerturbedRadialProfile
          (monopoleQuadraticRadius c) c rho ^ 4) r -
        3 * bubble r ^ 2| ≤
      (4 * K * (radialHartreeRowBoundConstant *
          monopoleRadialBoundConstant) +
        monopoleHartreePotentialBoundConstant * K ^ 2) * ell := by
  dsimp only
  let K : ℝ := hartreeKappa * M
  let c : ℝ := hartreeKappa * ell * m
  have hκ : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hK : 0 < K := mul_pos hκ hM
  have hRiesz0 : 0 ≤ radialHartreeRowBoundConstant *
      monopoleRadialBoundConstant :=
    mul_nonneg radialHartreeRowBoundConstant_pos.le
      monopoleRadialBoundConstant_pos.le
  have hRem0 : 0 ≤ monopoleHartreePotentialBoundConstant := by
    have hD := monopoleRadialBoundConstant_pos
    have hRow := radialHartreeBubbleBoundConstant_pos
    unfold monopoleHartreePotentialBoundConstant
      monopoleHartreeDensityDecayConstant
    positivity
  have hellOne : ell ≤ 1 := hellMax.trans (min_le_left _ _)
  have hellK : ell ≤ 1 / K := hellMax.trans (min_le_right _ _)
  have hcBound : |c| ≤ K * ell := by
    have hPos : 0 ≤ hartreeKappa * ell * m :=
      mul_nonneg (mul_nonneg hκ.le hell.le) hm
    calc
      |c| = hartreeKappa * ell * m := by
        dsimp [c]
        rw [abs_of_nonneg hPos]
      _ ≤ hartreeKappa * ell * M :=
        mul_le_mul_of_nonneg_left hmM
          (mul_nonneg hκ.le hell.le)
      _ = K * ell := by
        dsimp [K]
        ring
  have hcSmall : |c| ≤ 1 := by
    have hKEll : ell * K ≤ 1 :=
      (le_div_iff₀ hK).mp hellK
    calc
      |c| ≤ K * ell := hcBound
      _ = ell * K := by ring
      _ ≤ 1 := hKEll
  have hEllSq : ell ^ 2 ≤ ell := by
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr hellOne)]
  have hcSq : c ^ 2 ≤ K ^ 2 * ell := by
    calc
      c ^ 2 = |c| ^ 2 := (sq_abs c).symm
      _ ≤ (K * ell) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg c) hcBound 2
      _ = K ^ 2 * ell ^ 2 := by ring
      _ ≤ K ^ 2 * ell :=
        mul_le_mul_of_nonneg_left hEllSq (sq_nonneg K)
  have hCore := actual_Hartree_moving_monopole_core_Riesz_first_order
    c r hcSmall hr
  change |radialHartreePotential
      (fun rho => monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c rho ^ 4) r -
      3 * bubble r ^ 2| ≤
    (4 * K * (radialHartreeRowBoundConstant *
      monopoleRadialBoundConstant) +
      monopoleHartreePotentialBoundConstant * K ^ 2) * ell
  calc
    _ ≤ 4 * |c| * (radialHartreeRowBoundConstant *
          monopoleRadialBoundConstant) +
        monopoleHartreePotentialBoundConstant * c ^ 2 := hCore
    _ ≤ 4 * (K * ell) * (radialHartreeRowBoundConstant *
          monopoleRadialBoundConstant) +
        monopoleHartreePotentialBoundConstant * (K ^ 2 * ell) :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcBound (by norm_num))
          hRiesz0)
        (mul_le_mul_of_nonneg_left hcSq hRem0)
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
