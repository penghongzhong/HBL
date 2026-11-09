import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralOriginalPDEMismatch
import Mathlib.Tactic

/-!
# Spectral correction for the ACTUAL moving-parameter Kummer operator

Distinguish the two mathematically different physical differential
expressions: a fixed reference K(mu0,theta0) and the current frozen
coefficient with parameters (mu,theta). For the genuine Cramer/Volterra
correction w = u0 - G_K0[delta*u0], the unshifted reference residual is
FIRST order (-delta*u0); the CURRENT coefficient operator is exactly
L_K0 + delta and its residual is SECOND order (-delta*u1).

This is an exact original-Kummer coefficient identity, not an assertion
that the full nonlocal Hartree spacetime PDE equals either frozen
operator without additional time transport, modulation and Riesz terms.
No independently assigned source envelope, time order, or Type-II rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The corrected matched Green field solves the CURRENT (mu,theta)
Kummer equation up to the true SECOND-order spectral Volterra source.
The reference first-order source is exactly canceled by the *actual*
current-minus-reference zero-order coefficient delta. -/
theorem actual_Hartree_moving_coefficient_spectral_physical_PDE_exact
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a r0 r1 : ℝ) (ha : 0 < a)
    (hr0 : 0 < r0) (horder : r0 ≤ r1) (hr1 : r1 < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (U DU : ℂ) :
    let delta : ℂ := frozenZeroCoeff mu theta -
      frozenZeroCoeff mu0 theta0
    let u0 := actualOriginMatchedKummerValue K r0 r1 F U DU
    let u1 := actualOriginMatchedKummerValue K r0 r1
      (actualHartreeMatchedSpectralFirstSource K r0 r1 F U DU delta) 0 0
    let v := actualHartreeMatchedSpectralPhysicalValue K a r0 r1 F U DU delta
    ∀ y ∈ Ioo (0 : ℝ) (a * scale),
      actualMatchedScaledKummerApply mu theta a v y =
        ((a ^ 2)⁻¹ : ℝ) • (F (y / a) - delta * u1 (y / a)) := by
  dsimp only
  let delta : ℂ := frozenZeroCoeff mu theta -
    frozenZeroCoeff mu0 theta0
  let u0 := actualOriginMatchedKummerValue K r0 r1 F U DU
  let u1 := actualOriginMatchedKummerValue K r0 r1
    (actualHartreeMatchedSpectralFirstSource K r0 r1 F U DU delta) 0 0
  let v := actualHartreeMatchedSpectralPhysicalValue K a r0 r1 F U DU delta
  have hReference :=
    actual_Hartree_matched_spectral_original_physical_source
      K a r0 r1 ha hr0 horder hr1 F hF U DU delta
  have hDelta : frozenZeroCoeff mu theta =
      frozenZeroCoeff mu0 theta0 + delta := by
    dsimp [delta]
    ring
  have hOp (y : ℝ) :
      actualMatchedScaledKummerApply mu theta a v y =
        actualMatchedScaledKummerApply mu0 theta0 a v y +
          ((a ^ 2)⁻¹ : ℝ) • (delta * v y) := by
    unfold actualMatchedScaledKummerApply
    rw [hDelta]
    simp only [Complex.real_smul]
    ring
  intro y hy
  have hW : v y = u0 (y / a) - u1 (y / a) := rfl
  calc
    actualMatchedScaledKummerApply mu theta a v y =
        actualMatchedScaledKummerApply mu0 theta0 a v y +
          ((a ^ 2)⁻¹ : ℝ) • (delta * v y) := hOp y
    _ = ((a ^ 2)⁻¹ : ℝ) • (F (y / a) - delta * u0 (y / a)) +
          ((a ^ 2)⁻¹ : ℝ) • (delta * v y) := by
      rw [hReference y hy]
    _ = ((a ^ 2)⁻¹ : ℝ) • (F (y / a) - delta * u1 (y / a)) := by
      rw [hW]
      simp only [Complex.real_smul]
      ring

end HBL.TypeIIDynamicSelection
