import HBL.TypeIIDynamicSelection.ActualKummerRepairTrueBackgroundTimeGain
import HBL.TypeIIDynamicSelection.ActualKummerRepairCenterTimeGainOptimized
import Mathlib.Tactic

/-!
# Full true-background Hartree feedback with the improved source threshold

The SAME physical quartic outer-density difference, including its center
and off-center contributions, inherits order rho+kappa_center already when
rho >= (1+kappa_center)/2. This removes the unnecessary rho>=1 barrier
without suppressing D^3 or D^4 or adding cancellation assumptions.

The original stricter theorem is unchanged and remains backward compatible.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_Kummer_repair_true_background_full_potential_time_gain_optimized
    (ell a R B A c s beta rho CX CD r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hc : |c| ≤ 1)
    (hs : 1 ≤ s) (hbeta : 1 / 2 < beta)
    (hrho : (1 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius ell ≤ a * R)
    (hCX : 0 ≤ CX) (hXup : a * R ≤ CX * s)
    (hCD : 0 ≤ CD)
    (p q : ℂ)
    (hDtime : ‖p‖ + R * ‖q‖ ≤ CD * s ^ (-rho))
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hr : 0 < r) (hrOne : r ≤ 1) (hsep : 2 * r ≤ a * R) :
    let U : ℝ → ℂ := fun y =>
      (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
    let F := actualKummerPhysicalRepairOuterDensityDifference U a R p q
    let Ctime := actualKummerRepairTrueBackgroundTimeConstant B A CX CD
    let k := actualKummerRepairCenterTimeGain beta
    |radialHartreeExteriorPotential F (a * R) r| ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ctime) *
        s ^ (-(rho + k)) := by
  dsimp only
  let X : ℝ := a * R
  let M : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let S : ℝ := 2 * (B + A)
  let D0 : ℝ := ‖p‖ + R * ‖q‖
  let A0 : ℝ := actualHartreeKummerRepairBackgroundEnvelope ell a R B A
  let P0 : ℝ := actualKummerRepairDensityPolynomial A0 D0
  let Ctime : ℝ := actualKummerRepairTrueBackgroundTimeConstant B A CX CD
  let k : ℝ := actualKummerRepairCenterTimeGain beta
  let U : ℝ → ℂ := fun y =>
    (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
  let F : ℝ → ℝ :=
    actualKummerPhysicalRepairOuterDensityDifference U a R p q

  have hM : 0 ≤ M := by
    dsimp [M]
    have hm := monopoleRadialBoundConstant_pos.le
    linarith
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hD0 : 0 ≤ D0 := by
    dsimp [D0]
    positivity
  have hXpos : 0 < X := by
    dsimp [X]
    exact mul_pos ha hR
  have hLone : 1 ≤ actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hell hellOne (by norm_num)
  have hXone : 1 ≤ X := hLone.trans hXlow
  have hA0 : 0 ≤ A0 := by
    dsimp [A0]
    exact actual_Hartree_Kummer_repair_background_envelope_nonneg
      ell a R B A hell ha hR hB hA
  have hP0 : 0 ≤ P0 := by
    dsimp [P0]
    exact actual_Kummer_repair_density_polynomial_nonneg A0 D0 hA0 hD0
  have hCtime : 0 ≤ Ctime := by
    dsimp [Ctime, actualKummerRepairTrueBackgroundTimeConstant, M, S]
    positivity
  have hk : 0 < k := by
    dsimp [k]
    exact actual_Kummer_repair_center_time_gain_positive beta hbeta

  have hCenterPolyRaw :=
    actual_Kummer_repair_full_center_time_gain_optimized
      ell X M S D0 s beta rho CX CD
      hell hellOne hXlow hXup hM hS hD0 hCX hCD
      hs hbeta hrho htrap hDtime
  have hCenterPoly :
      X * P0 ≤ Ctime * s ^ (-(rho + k)) := by
    dsimp [P0, A0, Ctime, k, X, M, S,
      actualKummerRepairTrueBackgroundTimeConstant,
      actualHartreeKummerRepairBackgroundEnvelope,
      actualKummerRepairAbstractShellEnvelope] at hCenterPolyRaw ⊢
    simpa only [mul_assoc] using hCenterPolyRaw

  have hFeedback :=
    actual_Hartree_Kummer_repair_true_background_density_feedback
      ell a R B A c hell ha hR hB hA hc z hz hSup hStrauss p q
  have hCenterRaw :
      |radialHartreeExteriorCenter F X| ≤
        (4 * Real.pi * hartreeKappa) * (X * P0) := by
    dsimp [F, U, X, P0, A0, D0]
    simpa only [mul_assoc] using hFeedback.2.2.1
  have hHartree : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hCenter :
      |radialHartreeExteriorCenter F X| ≤
        ((4 * Real.pi * hartreeKappa) * Ctime) *
          s ^ (-(rho + k)) := by
    calc
      _ ≤ (4 * Real.pi * hartreeKappa) * (X * P0) := hCenterRaw
      _ ≤ (4 * Real.pi * hartreeKappa) *
          (Ctime * s ^ (-(rho + k))) :=
        mul_le_mul_of_nonneg_left hCenterPoly hHartree
      _ = _ := by ring

  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg r]
  have hXsq : 1 ≤ X ^ 2 := one_le_pow₀ hXone
  have hratio : r ^ 2 * (1 / X) ≤ X := by
    have hq : r ^ 2 / X ≤ X := by
      apply (div_le_iff₀ hXpos).2
      have : r ^ 2 ≤ X ^ 2 := hr2.trans hXsq
      simpa only [pow_two] using this
    simpa only [div_eq_mul_inv, one_mul] using hq
  have hGapRaw :
      |radialHartreeExteriorPotential F X r -
          radialHartreeExteriorCenter F X| ≤
        (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / X)) * P0 := by
    have h := hFeedback.2.2.2 r hr
    have hsep' : 2 * r ≤ X := by simpa only [X] using hsep
    have hh := h hsep'
    dsimp [F, U, X, P0, A0, D0] at hh ⊢
    simpa only [mul_assoc] using hh
  have hGapToCenterPoly :
      (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / X)) * P0 ≤
        (4 * Real.pi * hartreeKappa) * (X * P0) := by
    have hratio' :
        (4 * Real.pi * hartreeKappa) * (r ^ 2 * (1 / X)) ≤
          (4 * Real.pi * hartreeKappa) * X :=
      mul_le_mul_of_nonneg_left hratio hHartree
    have hp := mul_le_mul_of_nonneg_right hratio' hP0
    ring_nf at hp ⊢
    exact hp
  have hGap :
      |radialHartreeExteriorPotential F X r -
          radialHartreeExteriorCenter F X| ≤
        ((4 * Real.pi * hartreeKappa) * Ctime) *
          s ^ (-(rho + k)) := by
    calc
      _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / X)) * P0 :=
        hGapRaw
      _ ≤ (4 * Real.pi * hartreeKappa) * (X * P0) :=
        hGapToCenterPoly
      _ ≤ (4 * Real.pi * hartreeKappa) *
          (Ctime * s ^ (-(rho + k))) :=
        mul_le_mul_of_nonneg_left hCenterPoly hHartree
      _ = _ := by ring

  calc
    |radialHartreeExteriorPotential F X r| =
        |(radialHartreeExteriorPotential F X r -
            radialHartreeExteriorCenter F X) +
          radialHartreeExteriorCenter F X| := by
            congr 1
            ring
    _ ≤ |radialHartreeExteriorPotential F X r -
          radialHartreeExteriorCenter F X| +
        |radialHartreeExteriorCenter F X| :=
      abs_add_le _ _
    _ ≤ ((4 * Real.pi * hartreeKappa) * Ctime) *
          s ^ (-(rho + k)) +
        ((4 * Real.pi * hartreeKappa) * Ctime) *
          s ^ (-(rho + k)) :=
      add_le_add hGap hCenter
    _ = (2 * (4 * Real.pi * hartreeKappa) * Ctime) *
        s ^ (-(rho + k)) := by ring

end HBL.TypeIIDynamicSelection
