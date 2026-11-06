import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedSpeed
import Mathlib.Tactic

/-!
# Actual monopole+radiation background on the physical Kummer repair shell

For y in (aR,2aR] the true moving Hartree monopole has the global
(1+y)^(-1) decay and the critically rescaled physical radiation has the
global Strauss envelope (1+ell*y)^(-1)*sqrt(ell).

Keeping both lower-endpoint denominators gives the shell amplitude needed for
the complete quartic repair-density estimate.  No upper bound for a and no
Type-II limiting rate is inserted.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeKummerRepairBackgroundEnvelope
    (ell a R B A : ℝ) : ℝ :=
  (2 + 9 * monopoleRadialBoundConstant) / (1 + a * R) +
    (2 * (B + A) * Real.sqrt ell) / (1 + ell * (a * R))

theorem actual_Hartree_Kummer_repair_background_shell_envelope
    (ell a R B A c y : ℝ)
    (hell : 0 < ell) (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hc : |c| ≤ 1)
    (z : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hy : y ∈ Ioc (a * R) (2 * a * R)) :
    ‖(actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y‖ ≤
      actualHartreeKummerRepairBackgroundEnvelope ell a R B A := by
  let Cm : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let Cr : ℝ := 2 * (B + A)
  have hy0 : 0 < y := (mul_pos ha hR).trans hy.1
  have hCm : 0 ≤ Cm := by
    dsimp [Cm]
    have hm := monopoleRadialBoundConstant_pos.le
    linarith
  have hCr : 0 ≤ Cr := by
    dsimp [Cr]
    positivity
  have hVraw :=
    actual_Hartree_moving_monopole_one_plus_radius_decay c y hy0 hc
  have hLower : a * R ≤ y := hy.1.le
  have hDenMono : 0 < 1 + a * R := by positivity
  have hDenOrder : 1 + a * R ≤ 1 + y := by linarith
  have hV :
      |actualMomentLockedCore c y| ≤ Cm / (1 + a * R) := by
    apply (le_div_iff₀ hDenMono).2
    calc
      |actualMomentLockedCore c y| * (1 + a * R) ≤
          |actualMomentLockedCore c y| * (1 + y) :=
        mul_le_mul_of_nonneg_left hDenOrder (abs_nonneg _)
      _ = (1 + y) * |actualMomentLockedCore c y| := by ring
      _ ≤ Cm := by
        simpa only [Cm, actualMomentLockedCore] using hVraw
  have hZraw :=
    actual_Hartree_scaled_Strauss_global_radial_decay
      ell y B A hell hy0 hB hA z hSup hStrauss
  have hEllOrder : 1 + ell * (a * R) ≤ 1 + ell * y := by
    have hm := mul_le_mul_of_nonneg_left hLower hell.le
    linarith
  have hDenRad : 0 < 1 + ell * (a * R) := by positivity
  have hZ :
      ‖rescalePhysicalRadiation ell z y‖ ≤
        (Cr * Real.sqrt ell) / (1 + ell * (a * R)) := by
    apply (le_div_iff₀ hDenRad).2
    calc
      ‖rescalePhysicalRadiation ell z y‖ * (1 + ell * (a * R)) ≤
          ‖rescalePhysicalRadiation ell z y‖ * (1 + ell * y) :=
        mul_le_mul_of_nonneg_left hEllOrder (norm_nonneg _)
      _ = (1 + ell * y) * ‖rescalePhysicalRadiation ell z y‖ := by ring
      _ ≤ Cr * Real.sqrt ell := by
        simpa only [Cr] using hZraw
  calc
    ‖(actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y‖ ≤
      ‖(actualMomentLockedCore c y : ℂ)‖ +
        ‖rescalePhysicalRadiation ell z y‖ := norm_add_le _ _
    _ = |actualMomentLockedCore c y| +
        ‖rescalePhysicalRadiation ell z y‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Cm / (1 + a * R) +
        (Cr * Real.sqrt ell) / (1 + ell * (a * R)) :=
      add_le_add hV hZ
    _ = actualHartreeKummerRepairBackgroundEnvelope ell a R B A := by
      dsimp [actualHartreeKummerRepairBackgroundEnvelope, Cm, Cr]

theorem actual_Hartree_Kummer_repair_background_envelope_nonneg
    (ell a R B A : ℝ)
    (hell : 0 < ell) (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) :
    0 ≤ actualHartreeKummerRepairBackgroundEnvelope ell a R B A := by
  unfold actualHartreeKummerRepairBackgroundEnvelope
  have hm := monopoleRadialBoundConstant_pos.le
  positivity

end HBL.TypeIIDynamicSelection
