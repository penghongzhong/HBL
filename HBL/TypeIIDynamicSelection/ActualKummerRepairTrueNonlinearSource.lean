import HBL.TypeIIDynamicSelection.ActualKummerRepairTrueBackgroundTimeGainSqrtRadius
import HBL.TypeIIDynamicSelection.ActualHartreeComplexCubicLipschitz
import Mathlib.Tactic

/-!
# The full Hartree PDE source created by the physical Kummer repair tail

Previous strict estimates control the entire nonlocal quartic density
difference and its exterior potential, including cubic and quartic terms.
Here the potential is multiplied by the actual complex cubic factor
|V_c + Z_ell|^2 (V_c + Z_ell), as required by the ORIGINAL Hartree PDE.

The local cubic amplitude is DERIVED from global moving-monopole decay and
the physical radiation's high-regularity/Strauss envelope. No assumed
nonlinear multiplier, far-field cancellation, or prescribed Type-II rate.
This is an inner-core source producer, not a complete finite parametrix.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The unchanged true Hartree cubic on the physical core has a uniform
amplitude bound. The actual complex field is the moment-locked monopole
plus the critically rescaled physical radiation. -/
theorem actual_Hartree_repair_background_core_cubic_bound
    (ell B A c r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hc : |c| ≤ 1) (hr : 0 < r)
    (z : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let U : ℝ → ℂ := fun y =>
      (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A)
    ‖actualWholeRadiationLocalCubic U r‖ ≤ M ^ 3 := by
  dsimp only
  let Cm : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let Cr : ℝ := 2 * (B + A)
  let M : ℝ := Cm + Cr
  let U : ℝ → ℂ := fun y =>
    (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
  have hCm : 0 ≤ Cm := by
    dsimp [Cm]
    have hm := monopoleRadialBoundConstant_pos.le
    linarith
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hVraw :=
    actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hV :
      |actualMomentLockedCore c r| ≤ Cm := by
    have hVR : |actualMomentLockedCore c r| ≤
        (1 + r) * |actualMomentLockedCore c r| := by
      have hp : 0 ≤ r * |actualMomentLockedCore c r| :=
        mul_nonneg hr.le (abs_nonneg _)
      nlinarith only [hp]
    exact hVR.trans (by
      simpa only [Cm, actualMomentLockedCore] using hVraw)
  have hZraw :=
    actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss
  have hZR :
      ‖rescalePhysicalRadiation ell z r‖ ≤ Cr * Real.sqrt ell := by
    have hFirst :
        ‖rescalePhysicalRadiation ell z r‖ ≤
          (1 + ell * r) * ‖rescalePhysicalRadiation ell z r‖ := by
      have hp : 0 ≤ ell * r * ‖rescalePhysicalRadiation ell z r‖ :=
        mul_nonneg (mul_nonneg hell.le hr.le) (norm_nonneg _)
      nlinarith only [hp]
    exact hFirst.trans (by simpa only [Cr] using hZraw)
  have hsqrt : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hZ : ‖rescalePhysicalRadiation ell z r‖ ≤ Cr := by
    calc
      _ ≤ Cr * Real.sqrt ell := hZR
      _ ≤ Cr * 1 := mul_le_mul_of_nonneg_left hsqrt hCr
      _ = Cr := by ring
  have hU : ‖U r‖ ≤ M := by
    calc
      ‖U r‖ ≤ ‖(actualMomentLockedCore c r : ℂ)‖ +
          ‖rescalePhysicalRadiation ell z r‖ := norm_add_le _ _
      _ = |actualMomentLockedCore c r| +
          ‖rescalePhysicalRadiation ell z r‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ Cm + Cr := add_le_add hV hZ
      _ = M := rfl
  rw [actual_Hartree_complex_cubic_is_same_PDE_factor]
  unfold actualHartreeComplexCubic
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (‖U r‖))]
  calc
    ‖U r‖ ^ 2 * ‖U r‖ = ‖U r‖ ^ 3 := by ring
    _ ≤ M ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hU 3

/-- Realized genuine nonlocal Hartree PDE feedback from the same physical
Kummer repair tail, INCLUDING the unchanged cubic factor. The complete
quartic density is retained in the exterior potential. -/
theorem actual_Hartree_repair_full_nonlinear_PDE_source_sqrt_clock_gain
    (ell a R B A c s beta rho CX CD r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hc : |c| ≤ 1)
    (hs : 1 ≤ s) (hbeta : 1 / 2 < beta)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius ell ≤ a * R)
    (hCX : 0 ≤ CX) (hXup : a * R ≤ CX * s ^ (1 / 2 : ℝ))
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
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A)
    let k := actualKummerRepairCenterTimeGain beta
    ‖(radialHartreeExteriorPotential F (a * R) r : ℂ) *
        actualWholeRadiationLocalCubic U r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ctime * M ^ 3) *
        s ^ (-(rho + k)) := by
  dsimp only
  let U : ℝ → ℂ := fun y =>
    (actualMomentLockedCore c y : ℂ) + rescalePhysicalRadiation ell z y
  let F := actualKummerPhysicalRepairOuterDensityDifference U a R p q
  let Ctime := actualKummerRepairTrueBackgroundTimeConstant B A CX CD
  let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A)
  let k := actualKummerRepairCenterTimeGain beta
  have hPot :=
    actual_Hartree_Kummer_repair_true_background_full_potential_time_gain_sqrt_radius
      ell a R B A c s beta rho CX CD r
      hell hellOne ha hR hB hA hc hs hbeta hrho htrap
      hXlow hCX hXup hCD p q hDtime z hz hSup hStrauss hr hrOne hsep
  dsimp only at hPot
  have hCubic :=
    actual_Hartree_repair_background_core_cubic_bound
      ell B A c r hell hellOne hB hA hc hr z hSup hStrauss
  dsimp only at hCubic
  have hM : 0 ≤ M := by
    dsimp [M]
    have hm := monopoleRadialBoundConstant_pos.le
    positivity
  have hCtime : 0 ≤ Ctime := by
    have hMono : 0 ≤ 2 + 9 * monopoleRadialBoundConstant := by
      have hm := monopoleRadialBoundConstant_pos.le
      positivity
    have hRad : 0 ≤ 2 * (B + A) := by positivity
    dsimp [Ctime, actualKummerRepairTrueBackgroundTimeConstant]
    positivity
  have hCoef : 0 ≤ 2 * (4 * Real.pi * hartreeKappa) * Ctime := by
    unfold hartreeKappa
    positivity
  have hPow : 0 ≤ s ^ (-(rho + k)) :=
    Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ s) _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |radialHartreeExteriorPotential F (a * R) r| *
        ‖actualWholeRadiationLocalCubic U r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ctime *
        s ^ (-(rho + k))) *
        ‖actualWholeRadiationLocalCubic U r‖ :=
      mul_le_mul_of_nonneg_right
        (by simpa only [F, U, Ctime, k] using hPot)
        (norm_nonneg _)
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ctime *
          s ^ (-(rho + k))) * M ^ 3 :=
      mul_le_mul_of_nonneg_left
        (by simpa only [U, M] using hCubic)
        (mul_nonneg hCoef hPow)
    _ = (2 * (4 * Real.pi * hartreeKappa) * Ctime * M ^ 3) *
          s ^ (-(rho + k)) := by ring

end HBL.TypeIIDynamicSelection
