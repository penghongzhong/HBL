import HBL.TypeIIDynamicSelection.ActualHartreePhysicalPlateauMovingSpectralQuadraticShellGain
import Mathlib.Tactic

/-!
# From a true Hartree plateau spectral shell to renormalized-time gain

The preceding source-specific strict theorem proves the spatial factor
  R^(-19/4), R=ell^(-1/16)/2.
This module converts that *known physical factor* into a positive
renormalized-time gain under an explicitly visible intermediate
bootstrap trap ell(s) <= s^(-beta), beta>1/2.

A source-order hypothesis D <= C*s^(-rho) is an induction input on
the *original* Fredholm source norm D, not an assumed improvement of
the new PDE residual. This lemma does not construct or propagate the
bootstrap trap, and does not bound other four-piece PDE residuals.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

def actualHartreePlateauSpectralTimeGain (beta : ℝ) : ℝ :=
  19 * beta / 64

theorem actual_Hartree_plateau_spectral_time_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    0 < actualHartreePlateauSpectralTimeGain beta := by
  unfold actualHartreePlateauSpectralTimeGain
  linarith

/-- Genuine moving shell radius gives ell^(19/64), not an assumed
time-order input. The last inequality uses only the stated trap. -/
theorem actual_Hartree_plateau_spectral_shell_trapped_time_factor
    (s ell beta : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell)
    (htrap : ell ≤ s ^ (-beta)) :
    (actualHartreeSlowInnerRadius ell / 2) ^ (-(19 / 4 : ℝ)) ≤
      (2 : ℝ) ^ (19 / 4 : ℝ) *
        s ^ (-actualHartreePlateauSpectralTimeGain beta) := by
  have hellr : 0 ≤ ell ^ (-(1 / 16 : ℝ)) :=
    (Real.rpow_pos_of_pos hell _).le
  have htwo : 0 ≤ (2 : ℝ) := by norm_num
  have hmul :
      (ell ^ (-(1 / 16 : ℝ))) ^ (-(19 / 4 : ℝ)) =
        ell ^ (19 / 64 : ℝ) := by
    calc
      _ = ell ^ ((-(1 / 16 : ℝ)) * (-(19 / 4 : ℝ))) :=
        (Real.rpow_mul hell.le _ _).symm
      _ = ell ^ (19 / 64 : ℝ) := by
        congr 1
        norm_num
  have hexact :
      (actualHartreeSlowInnerRadius ell / 2) ^ (-(19 / 4 : ℝ)) =
        (2 : ℝ) ^ (19 / 4 : ℝ) * ell ^ (19 / 64 : ℝ) := by
    unfold actualHartreeSlowInnerRadius
    rw [Real.div_rpow hellr htwo (-(19 / 4 : ℝ)), hmul]
    rw [Real.rpow_neg htwo (19 / 4 : ℝ)]
    simp only [div_inv_eq_mul]
    ring
  have hsnonneg : 0 ≤ s := by linarith
  have hpower :
      ell ^ (19 / 64 : ℝ) ≤
        s ^ (-actualHartreePlateauSpectralTimeGain beta) := by
    calc
      ell ^ (19 / 64 : ℝ) ≤
          (s ^ (-beta)) ^ (19 / 64 : ℝ) :=
        Real.rpow_le_rpow hell.le htrap (by norm_num)
      _ = s ^ (-actualHartreePlateauSpectralTimeGain beta) := by
        rw [← Real.rpow_mul hsnonneg]
        congr 1
        unfold actualHartreePlateauSpectralTimeGain
        ring
  calc
    _ = (2 : ℝ) ^ (19 / 4 : ℝ) * ell ^ (19 / 64 : ℝ) := hexact
    _ ≤ (2 : ℝ) ^ (19 / 4 : ℝ) *
          s ^ (-actualHartreePlateauSpectralTimeGain beta) :=
      mul_le_mul_of_nonneg_left hpower
        (Real.rpow_nonneg htwo _)

/-- An actual Fredholm source norm D at order rho, combined with the
strict source-specific spectral-shell factor, gains 19*beta/64 in time.
No independent new-residual estimate is assumed in the hypothesis. -/
theorem actual_Hartree_plateau_spectral_shell_source_to_time_gain
    (s ell beta rho A C D : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell)
    (htrap : ell ≤ s ^ (-beta))
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hsource : D ≤ C * s ^ (-rho)) :
    A * (actualHartreeSlowInnerRadius ell / 2) ^ (-(19 / 4 : ℝ)) * D ≤
      (A * (2 : ℝ) ^ (19 / 4 : ℝ) * C) *
        s ^ (-(rho + actualHartreePlateauSpectralTimeGain beta)) := by
  have hspos : 0 < s := by linarith
  have hfactor :=
    actual_Hartree_plateau_spectral_shell_trapped_time_factor
      s ell beta hs hell htrap
  have htwononneg : 0 ≤ (2 : ℝ) ^ (19 / 4 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have htime_nonneg :
      0 ≤ s ^ (-actualHartreePlateauSpectralTimeGain beta) :=
    Real.rpow_nonneg hspos.le _
  have hmul_nonneg :
      0 ≤ A * ((2 : ℝ) ^ (19 / 4 : ℝ) *
        s ^ (-actualHartreePlateauSpectralTimeGain beta)) :=
    mul_nonneg hA (mul_nonneg htwononneg htime_nonneg)
  have hpow :
      s ^ (-actualHartreePlateauSpectralTimeGain beta) * s ^ (-rho) =
      s ^ (-(rho + actualHartreePlateauSpectralTimeGain beta)) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  calc
    A * (actualHartreeSlowInnerRadius ell / 2) ^ (-(19 / 4 : ℝ)) * D ≤
      A * ((2 : ℝ) ^ (19 / 4 : ℝ) *
        s ^ (-actualHartreePlateauSpectralTimeGain beta)) * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor hA) hD
    _ ≤ A * ((2 : ℝ) ^ (19 / 4 : ℝ) *
          s ^ (-actualHartreePlateauSpectralTimeGain beta)) *
          (C * s ^ (-rho)) :=
      mul_le_mul_of_nonneg_left hsource hmul_nonneg
    _ = (A * (2 : ℝ) ^ (19 / 4 : ℝ) * C) *
          s ^ (-(rho + actualHartreePlateauSpectralTimeGain beta)) := by
      rw [← hpow]
      ring

end HBL.TypeIIDynamicSelection
