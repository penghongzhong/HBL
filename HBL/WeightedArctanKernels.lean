import HBL.WeightedHartreeBirmanSchwinger
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
Pointwise kernel identities for the change of variables `r = tan θ`.

The unitary change of variables used in the weighted spectral bridge sends
the half-line to `(0, π/2)`.  This file records the algebraic part of that
conjugation independently of the later change-of-measure argument.
-/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.Modulation
open HBL.Modulation.AffineTail

/-- Logarithmic Hartree kernel on the angular interval. -/
def angularHartreeLog (theta phi : ℝ) : ℝ :=
  Real.log
    (Real.sin (theta + phi) / |Real.sin (theta - phi)|)

/-- Dirichlet Green kernel of `-∂²-1` on `(0, π/2)`. -/
def angularFreeGreen (theta phi : ℝ) : ℝ :=
  Real.sin (min theta phi) * Real.cos (max theta phi)

theorem bubble_eq_cos_arctan (r : ℝ) :
    bubble r = Real.cos (Real.arctan r) := by
  simp [bubble, Real.cos_arctan, one_div]

theorem weightedGreenDecay_eq_cos_arctan_sq (r : ℝ) :
    (1 + r ^ 2)⁻¹ = Real.cos (Real.arctan r) ^ 2 := by
  rw [Real.cos_sq_arctan]
  simp [one_div]

theorem sin_arctan_eq_mul_cos_arctan (r : ℝ) :
    Real.sin (Real.arctan r) =
      r * Real.cos (Real.arctan r) := by
  rw [Real.sin_arctan, Real.cos_arctan]
  ring

theorem sin_arctan_add (r rho : ℝ) :
    Real.sin (Real.arctan r + Real.arctan rho) =
      (r + rho) * bubble r * bubble rho := by
  rw [Real.sin_add, Real.sin_arctan r, Real.cos_arctan r,
    Real.sin_arctan rho, Real.cos_arctan rho]
  unfold bubble
  ring

theorem sin_arctan_sub (r rho : ℝ) :
    Real.sin (Real.arctan r - Real.arctan rho) =
      (r - rho) * bubble r * bubble rho := by
  rw [Real.sin_sub, Real.sin_arctan r, Real.cos_arctan r,
    Real.sin_arctan rho, Real.cos_arctan rho]
  unfold bubble
  ring

theorem arctan_log_ratio
    (r rho : ℝ) (hdiag : r ≠ rho) :
    (r + rho) / |r - rho| =
      Real.sin (Real.arctan r + Real.arctan rho) /
        |Real.sin (Real.arctan r - Real.arctan rho)| := by
  rw [sin_arctan_add, sin_arctan_sub]
  have hbposr : 0 < bubble r := by
    unfold bubble
    positivity
  have hbposrho : 0 < bubble rho := by
    unfold bubble
    positivity
  have hbr : bubble r ≠ 0 := by
    exact hbposr.ne'
  have hbρ : bubble rho ≠ 0 := by
    exact hbposrho.ne'
  have hsub : |r - rho| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hdiag)
  simp only [abs_mul, abs_of_pos hbposr, abs_of_pos hbposrho]
  field_simp [hbr, hbρ, hsub]

theorem hartreeRadialLog_eq_angular
    (r rho : ℝ) (hdiag : r ≠ rho) :
    hartreeRadialLog r rho =
      angularHartreeLog (Real.arctan r) (Real.arctan rho) := by
  unfold hartreeRadialLog angularHartreeLog
  rw [arctan_log_ratio r rho hdiag]

theorem weightedHartreeKernel_eq_angular
    (r rho : ℝ) (hdiag : r ≠ rho) :
    weightedHartreeKernel r rho =
      (24 / Real.pi) * bubble r * bubble rho *
        angularHartreeLog (Real.arctan r) (Real.arctan rho) := by
  unfold weightedHartreeKernel
  rw [hartreeRadialLog_eq_angular r rho hdiag]
  unfold hartreeKappa
  field_simp [Real.pi_ne_zero]
  ring

theorem weightedFreeGreen_eq_angular (r rho : ℝ) :
    weightedFreeGreen r rho =
      bubble r * bubble rho *
        angularFreeGreen (Real.arctan r) (Real.arctan rho) := by
  rcases le_total r rho with h | h
  · have ha : Real.arctan r ≤ Real.arctan rho :=
      Real.arctan_mono h
    rw [weightedFreeGreen, angularFreeGreen, min_eq_left h,
      min_eq_left ha, max_eq_right ha,
      weightedGreenDecay_eq_cos_arctan_sq,
      weightedGreenDecay_eq_cos_arctan_sq,
      bubble_eq_cos_arctan, bubble_eq_cos_arctan,
      sin_arctan_eq_mul_cos_arctan]
    ring
  · have ha : Real.arctan rho ≤ Real.arctan r :=
      Real.arctan_mono h
    rw [weightedFreeGreen, angularFreeGreen, min_eq_right h,
      min_eq_right ha, max_eq_left ha,
      weightedGreenDecay_eq_cos_arctan_sq,
      weightedGreenDecay_eq_cos_arctan_sq,
      bubble_eq_cos_arctan, bubble_eq_cos_arctan,
      sin_arctan_eq_mul_cos_arctan]
    ring

end HBL.Modulation.Monopole
