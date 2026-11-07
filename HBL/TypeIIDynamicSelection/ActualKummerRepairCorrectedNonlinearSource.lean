import HBL.TypeIIDynamicSelection.ActualKummerRepairCorrectedBackgroundTimeGain
import HBL.TypeIIDynamicSelection.ActualKummerRepairTrueNonlinearSource
import Mathlib.Tactic

/-!
# Genuine corrected-background nonlinear Hartree Kummer source

The true iterated background is V_c + Z_ell + H, where H is a previously
constructed physical profile correction. The nonlocal repair feedback
must be multiplied by |V_c+Z_ell+H|^2 (V_c+Z_ell+H), not by the cubic
of the uncorrected background. We prove its concrete core bound from
the same radial field and the complete potential source gain.

All quartic cross terms, the nonlinear local cubic, and the physical
sqrt-clock radius remain present. No parametrix is assumed to exist.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_repair_corrected_background_core_cubic_bound
    (ell B A CH c r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hc : |c| ≤ 1) (hr : 0 < r)
    (z H : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hH : ∀ u : ℝ, 0 < u → ‖H u‖ ≤ CH * bubble u) :
    let U : ℝ → ℂ := fun y =>
      ((actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y) + H y
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
    ‖actualWholeRadiationLocalCubic U r‖ ≤ M ^ 3 := by
  dsimp only
  let Cm : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let Cr : ℝ := 2 * (B + A)
  let M : ℝ := Cm + Cr + CH
  let U : ℝ → ℂ := fun y =>
    ((actualMomentLockedCore c y : ℂ) +
      rescalePhysicalRadiation ell z y) + H y
  have hCm : 0 ≤ Cm := by
    dsimp [Cm]
    have hm := monopoleRadialBoundConstant_pos.le
    linarith
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hM : 0 ≤ M := add_nonneg (add_nonneg hCm hCr) hCH
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
  have hHpoint : ‖H r‖ ≤ CH := by
    calc
      _ ≤ CH * bubble r := hH r hr
      _ ≤ CH * 1 :=
        mul_le_mul_of_nonneg_left (bubble_le_one r) hCH
      _ = CH := by ring
  have hU : ‖U r‖ ≤ M := by
    calc
      ‖U r‖ ≤ ‖(actualMomentLockedCore c r : ℂ) +
          rescalePhysicalRadiation ell z r‖ + ‖H r‖ :=
        norm_add_le _ _
      _ ≤ (‖(actualMomentLockedCore c r : ℂ)‖ +
          ‖rescalePhysicalRadiation ell z r‖) + ‖H r‖ :=
        add_le_add_right (norm_add_le _ _) _
      _ = (|actualMomentLockedCore c r| +
          ‖rescalePhysicalRadiation ell z r‖) + ‖H r‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (Cm + Cr) + CH :=
        add_le_add (add_le_add hV hZ) hHpoint
      _ = M := rfl
  rw [actual_Hartree_complex_cubic_is_same_PDE_factor]
  unfold actualHartreeComplexCubic
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (‖U r‖))]
  calc
    ‖U r‖ ^ 2 * ‖U r‖ = ‖U r‖ ^ 3 := by ring
    _ ≤ M ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hU 3

/-- Complete nonlocal Hartree PDE source, including its genuine cubic on
V_c+Z_ell+H and the full quartic density of the moving Kummer repair. -/
theorem actual_Hartree_Kummer_corrected_full_nonlinear_source_time_gain
    (ell a R B A CH c s beta rho CX CD r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hc : |c| ≤ 1)
    (hs : 1 ≤ s) (hbeta : 1 / 2 < beta)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius ell ≤ a * R)
    (hCX : 0 ≤ CX) (hXup : a * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hCD : 0 ≤ CD)
    (p q : ℂ)
    (hDtime : ‖p‖ + R * ‖q‖ ≤ CD * s ^ (-rho))
    (z H : ℝ → ℂ) (hz : Measurable z) (hHmeas : Measurable H)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hHCorr : ∀ u : ℝ, 0 < u → ‖H u‖ ≤ CH * bubble u)
    (hr : 0 < r) (hrOne : r ≤ 1) (hsep : 2 * r ≤ a * R) :
    let U : ℝ → ℂ := fun y =>
      ((actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y) + H y
    let F := actualKummerPhysicalRepairOuterDensityDifference U a R p q
    let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX CD
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
    let k := actualKummerRepairCenterTimeGain beta
    ‖(radialHartreeExteriorPotential F (a * R) r : ℂ) *
        actualWholeRadiationLocalCubic U r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
        s ^ (-(rho + k)) := by
  dsimp only
  let U : ℝ → ℂ := fun y =>
    ((actualMomentLockedCore c y : ℂ) +
      rescalePhysicalRadiation ell z y) + H y
  let F : ℝ → ℝ :=
    actualKummerPhysicalRepairOuterDensityDifference U a R p q
  let Ct : ℝ := actualKummerRepairCorrectedTimeConstant B A CH CX CD
  let M : ℝ :=
    2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
  let k : ℝ := actualKummerRepairCenterTimeGain beta
  have hPot :=
    actual_Hartree_Kummer_repair_corrected_background_full_potential_time_gain
      ell a R B A CH c s beta rho CX CD r
      hell hellOne ha hR hB hA hCH hc hs hbeta hrho htrap
      hXlow hCX hXup hCD p q hDtime z H hz hHmeas
      hSup hStrauss hHCorr hr hrOne hsep
  dsimp only at hPot
  have hCubic :=
    actual_Hartree_repair_corrected_background_core_cubic_bound
      ell B A CH c r hell hellOne hB hA hCH hc hr z H
      hSup hStrauss hHCorr
  dsimp only at hCubic
  have hMono : 0 ≤ monopoleRadialBoundConstant :=
    monopoleRadialBoundConstant_pos.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hCt : 0 ≤ Ct := by
    dsimp [Ct, actualKummerRepairCorrectedTimeConstant]
    positivity
  have hCoef : 0 ≤ 2 * (4 * Real.pi * hartreeKappa) * Ct := by
    unfold hartreeKappa
    positivity
  have hPow : 0 ≤ s ^ (-(rho + k)) :=
    Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ s) _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |radialHartreeExteriorPotential F (a * R) r| *
        ‖actualWholeRadiationLocalCubic U r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ct *
        s ^ (-(rho + k))) * ‖actualWholeRadiationLocalCubic U r‖ :=
      mul_le_mul_of_nonneg_right
        (by simpa only [F, U, Ct, k] using hPot)
        (norm_nonneg _)
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ct *
          s ^ (-(rho + k))) * M ^ 3 :=
      mul_le_mul_of_nonneg_left
        (by simpa only [U, M] using hCubic)
        (mul_nonneg hCoef hPow)
    _ = (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
          s ^ (-(rho + k)) := by ring

end HBL.TypeIIDynamicSelection
