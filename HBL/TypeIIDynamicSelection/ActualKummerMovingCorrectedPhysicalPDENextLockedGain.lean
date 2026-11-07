import HBL.TypeIIDynamicSelection.ActualKummerRepairCorrectedBackgroundTimeGain
import HBL.TypeIIDynamicSelection.ActualKummerRepairTrueNonlinearSource
import HBL.TypeIIDynamicSelection.ActualHartreeLockedPhysicalGain
import Mathlib.Tactic

/-!
# Genuine corrected-background moving Kummer residual has next-layer order

The old repair source estimate treated only V_c+Z_ell. Here the very same
physical PDE is evaluated on V_c+Z_ell+H, where H is the current nonlinear
profile correction. Its complete nonlocal quartic density and the true
complex cubic multiplier are both retained, including H cross interactions.
All source estimates are derived from the original physical monopole,
actual radiation Strauss envelope and the already constructed correction.
The moving repair vanishes locally in the inner core but changes the Riesz
potential; thus this is an original full-PDE residual difference, not a
synthetic linear forcing or a declared gain tag.

The theorem controls the inner core for r<=1 and 2r<=aR, NOT the entire
three-region finite-profile parametrix or the final Type-II orbit.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact physical local cubic amplitude on V_c+Z_ell+H. Unlike the global
row-dominating envelope, the constant does not lose a power of ell^{-1}. -/
theorem actual_Hartree_corrected_repair_core_cubic_bound
    (ell c r B A CH : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hc : |c| ≤ 1) (hr : 0 < r)
    (z H : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hHCorr : ∀ u : ℝ, 0 < u → ‖H u‖ ≤ CH * bubble u) :
    let U : ℝ → ℂ := fun y =>
      (actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y + H y
    let M := 2 + 9 * monopoleRadialBoundConstant +
      2 * (B + A) + CH
    ‖actualWholeRadiationLocalCubic U r‖ ≤ M ^ 3 := by
  dsimp only
  let Cm : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let Cr : ℝ := 2 * (B + A)
  let M : ℝ := Cm + Cr + CH
  let U : ℝ → ℂ := fun y =>
    (actualMomentLockedCore c y : ℂ) +
      rescalePhysicalRadiation ell z y + H y
  have hCm : 0 ≤ Cm := by
    dsimp [Cm]
    have hm := monopoleRadialBoundConstant_pos.le
    positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hVraw :=
    actual_Hartree_moment_locked_core_bubble_envelope c r hr hc
  have hV : ‖(actualMomentLockedCore c r : ℂ)‖ ≤ Cm := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      |actualMomentLockedCore c r| ≤ Cm * bubble r := by
        simpa only [Cm] using hVraw
      _ ≤ Cm * 1 :=
        mul_le_mul_of_nonneg_left (bubble_le_one r) hCm
      _ = Cm := by ring
  have hZraw :=
    actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss
  have hZfirst :
      ‖rescalePhysicalRadiation ell z r‖ ≤
        (1 + ell * r) * ‖rescalePhysicalRadiation ell z r‖ := by
    have hp : 0 ≤ ell * r * ‖rescalePhysicalRadiation ell z r‖ :=
      mul_nonneg (mul_nonneg hell.le hr.le) (norm_nonneg _)
    nlinarith only [hp]
  have hSqrt : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hZ : ‖rescalePhysicalRadiation ell z r‖ ≤ Cr := by
    calc
      _ ≤ (1 + ell * r) * ‖rescalePhysicalRadiation ell z r‖ :=
        hZfirst
      _ ≤ Cr * Real.sqrt ell := by
        simpa only [Cr] using hZraw
      _ ≤ Cr * 1 := mul_le_mul_of_nonneg_left hSqrt hCr
      _ = Cr := by ring
  have hH : ‖H r‖ ≤ CH := by
    calc
      _ ≤ CH * bubble r := hHCorr r hr
      _ ≤ CH * 1 := mul_le_mul_of_nonneg_left (bubble_le_one r) hCH
      _ = CH := by ring
  have hU : ‖U r‖ ≤ M := by
    calc
      ‖U r‖ ≤ ‖(actualMomentLockedCore c r : ℂ)‖ +
          ‖rescalePhysicalRadiation ell z r‖ + ‖H r‖ := by
        dsimp [U]
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ Cm + Cr + CH := add_le_add (add_le_add hV hZ) hH
      _ = M := rfl
  rw [actual_Hartree_complex_cubic_is_same_PDE_factor]
  unfold actualHartreeComplexCubic
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (‖U r‖))]
  calc
    ‖U r‖ ^ 2 * ‖U r‖ = ‖U r‖ ^ 3 := by ring
    _ ≤ M ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hU 3

/-- Inner-core ORIGINAL Hartree PDE residual from adding the moving
Kummer replacement to the current corrected background. Every quartic
density cross term involving H is present in the exact source identity
and the genuine physical nonlocal positive-order estimate. -/
theorem actual_Hartree_moving_corrected_Kummer_full_PDE_next_locked_gain
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z H : ℝ → ℝ → ℂ)
    (b omega s r B A CH beta rhoStar rho CX CD : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : ContinuousAt a s) (hR : 0 < R)
    (hell : 0 < ell s) (hellOne : ell s ≤ 1)
    (hc : |c s| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hs : 1 ≤ s)
    (hbeta : 1 / 2 < beta)
    (_hrhoStar : 0 < rhoStar)
    (_hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell s ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius (ell s) ≤ a s * R)
    (hCX : 0 ≤ CX) (hXup : a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hCD : 0 ≤ CD)
    (hJet : ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho))
    (hz : Measurable (z (time s))) (hHmeas : Measurable (H s))
    (hSup : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hHCorr : ∀ u : ℝ, 0 < u → ‖H s u‖ ≤ CH * bubble u)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hsep : 2 * r ≤ a s * R) :
    let U : ℝ → ℝ → ℂ := fun t y =>
      (actualMomentLockedCore (c t) y : ℂ) +
        rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
    let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX CD
    let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
    let kl := actualHartreeLockedKappa beta rhoStar
    ‖complexRadialRenormalizedResidual
        (fun t y => U t y + actualKummerPhysicalOuterRepair a R p q t y)
        b omega s r -
      complexRadialRenormalizedResidual U b omega s r‖ ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
        s ^ (-(rho + kl)) := by
  dsimp only
  let U : ℝ → ℝ → ℂ := fun t y =>
    (actualMomentLockedCore (c t) y : ℂ) +
      rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
  let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX CD
  let M := 2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
  let kl := actualHartreeLockedKappa beta rhoStar
  let kc := actualKummerRepairCenterTimeGain beta
  have hExact :=
    actual_Kummer_moving_repair_corrected_Hartree_core_PDE_exact
      a ell c time R p q z H b omega s r B A CH
      ha haCont hR hell hellOne hc hB hA hCH hr hsep
      hz hHmeas hSup hStrauss hHCorr
  dsimp only at hExact
  have hPot :=
    actual_Hartree_Kummer_repair_corrected_background_full_potential_time_gain
      (ell s) (a s) R B A CH (c s) s beta rho CX CD r
      hell hellOne (ha s) hR hB hA hCH hc hs hbeta hrho htrap
      hXlow hCX hXup hCD (p s) (q s) hJet
      (z (time s)) (H s) hz hHmeas hSup hStrauss hHCorr
      hr hrOne hsep
  dsimp only at hPot
  have hCubic :=
    actual_Hartree_corrected_repair_core_cubic_bound
      (ell s) (c s) r B A CH
      hell hellOne hB hA hCH hc hr
      (z (time s)) (H s) hSup hStrauss hHCorr
  dsimp only at hCubic
  have hCt : 0 ≤ Ct := by
    have hMono : 0 ≤ monopoleRadialBoundConstant :=
      monopoleRadialBoundConstant_pos.le
    dsimp [Ct, actualKummerRepairCorrectedTimeConstant]
    positivity
  have hCoef :
      0 ≤ 2 * (4 * Real.pi * hartreeKappa) * Ct := by
    unfold hartreeKappa
    positivity
  have hPow0 : 0 ≤ s ^ (-(rho + kc)) :=
    Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ s) _
  have hNonlinear :
      ‖(radialHartreeExteriorPotential
          (actualKummerPhysicalRepairOuterDensityDifference
            (U s) (a s) R (p s) (q s)) (a s * R) r : ℂ) *
            actualWholeRadiationLocalCubic (U s) r‖ ≤
        (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
          s ^ (-(rho + kc)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |radialHartreeExteriorPotential
          (actualKummerPhysicalRepairOuterDensityDifference
            (U s) (a s) R (p s) (q s)) (a s * R) r| *
        ‖actualWholeRadiationLocalCubic (U s) r‖ ≤
          (2 * (4 * Real.pi * hartreeKappa) * Ct *
            s ^ (-(rho + kc))) *
            ‖actualWholeRadiationLocalCubic (U s) r‖ :=
          mul_le_mul_of_nonneg_right
            (by simpa only [U, Ct, kc] using hPot)
            (norm_nonneg _)
      _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ct *
            s ^ (-(rho + kc))) * M ^ 3 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [U, M] using hCubic)
          (mul_nonneg hCoef hPow0)
      _ = (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
            s ^ (-(rho + kc)) := by ring
  have hK : kl ≤ kc :=
    actual_Hartree_locked_kappa_le_repair beta rhoStar
  have hPow : s ^ (-(rho + kc)) ≤ s ^ (-(rho + kl)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have hBigCoef :
      0 ≤ 2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3 := by
    have hm := monopoleRadialBoundConstant_pos.le
    dsimp [M]
    unfold hartreeKappa
    positivity
  calc
    _ = ‖(radialHartreeExteriorPotential
          (actualKummerPhysicalRepairOuterDensityDifference
            (U s) (a s) R (p s) (q s)) (a s * R) r : ℂ) *
            actualWholeRadiationLocalCubic (U s) r‖ := by
      rw [hExact]
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
          s ^ (-(rho + kc)) := hNonlinear
    _ ≤ (2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3) *
          s ^ (-(rho + kl)) :=
      mul_le_mul_of_nonneg_left hPow hBigCoef

end HBL.TypeIIDynamicSelection
