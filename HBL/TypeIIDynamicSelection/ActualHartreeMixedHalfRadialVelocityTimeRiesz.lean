import HBL.TypeIIDynamicSelection.ActualHartreeHalfRadialVelocityTimeRiesz
import Mathlib.Tactic

/-!
# Genuine mixed original Hartree time source from physical half-radial velocities

For the actual real core V and complex radiation z,
  M(V,z)=|V+z|^4-|V|^4-|z|^4.
The full time velocity is a difference of three genuine quartic velocities.
The original half-radial field and time-velocity envelopes imply that
THIS mixed quartic velocity has bubble-squared decay, so the already
verified original radial inverse-square Riesz row yields a uniform
potential-time derivative bound at every positive observation radius.

This is not a prescribed time decay or a synthetic local Hartree source:
the full nonlocal logarithmic kernel is retained. Constructing all
half-radial bounds on one actual four-region PDE orbit remains open.
The strict build imports the corrected physical half-radial velocity
producer; no original 13-environment acceptance is claimed here.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Quantitative pointwise original mixed quartic velocity, deduced
from the real/complex SAME-orbit field and time velocities. -/
theorem actual_Hartree_original_mixed_quartic_velocity_half_radial
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (s Mv Mz Dv Dz : ℝ)
    (hMv : 0 ≤ Mv) (hMz : 0 ≤ Mz)
    (hDv : 0 ≤ Dv) (hDz : 0 ≤ Dz)
    (hV : ∀ r : ℝ, 0 < r →
      |V s r| ≤ Mv * Real.sqrt (bubble r))
    (hDV : ∀ r : ℝ, 0 < r →
      |dV s r| ≤ Dv * Real.sqrt (bubble r))
    (hZ : ∀ r : ℝ, 0 < r →
      ‖z s r‖ ≤ Mz * Real.sqrt (bubble r))
    (hDZ : ∀ r : ℝ, 0 < r →
      ‖dz s r‖ ≤ Dz * Real.sqrt (bubble r)) :
    ∀ r : ℝ, 0 < r →
      |actualHartreeMixedQuarticTimeVelocity V dV z dz s r| ≤
      (8 * ((Mv + Mz) ^ 3 * (Dv + Dz) +
        Mv ^ 3 * Dv + Mz ^ 3 * Dz)) * bubble r ^ 2 := by
  have hU : ∀ r : ℝ, 0 < r →
      ‖(V s r : ℂ) + z s r‖ ≤
        (Mv + Mz) * Real.sqrt (bubble r) := by
    intro r hr
    calc
      ‖(V s r : ℂ) + z s r‖ ≤ ‖(V s r : ℂ)‖ + ‖z s r‖ :=
        norm_add_le _ _
      _ ≤ Mv * Real.sqrt (bubble r) +
          Mz * Real.sqrt (bubble r) := by
            exact add_le_add
              (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hV r hr)
              (hZ r hr)
      _ = (Mv + Mz) * Real.sqrt (bubble r) := by ring
  have hDU : ∀ r : ℝ, 0 < r →
      ‖(dV s r : ℂ) + dz s r‖ ≤
        (Dv + Dz) * Real.sqrt (bubble r) := by
    intro r hr
    calc
      ‖(dV s r : ℂ) + dz s r‖ ≤ ‖(dV s r : ℂ)‖ + ‖dz s r‖ :=
        norm_add_le _ _
      _ ≤ Dv * Real.sqrt (bubble r) +
          Dz * Real.sqrt (bubble r) := by
            exact add_le_add
              (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hDV r hr)
              (hDZ r hr)
      _ = (Dv + Dz) * Real.sqrt (bubble r) := by ring
  have hTot :=
    actual_Hartree_original_quartic_velocity_half_radial_to_bubble_sq
      (fun r => (V s r : ℂ) + z s r)
      (fun r => (dV s r : ℂ) + dz s r)
      (Mv + Mz) (Dv + Dz)
      (add_nonneg hMv hMz) (add_nonneg hDv hDz) hU hDU
  have hCore :=
    actual_Hartree_original_quartic_velocity_half_radial_to_bubble_sq
      (fun r => (V s r : ℂ))
      (fun r => (dV s r : ℂ))
      Mv Dv hMv hDv
      (by intro r hr
          simpa only [Complex.norm_real, Real.norm_eq_abs] using hV r hr)
      (by intro r hr
          simpa only [Complex.norm_real, Real.norm_eq_abs] using hDV r hr)
  have hRad :=
    actual_Hartree_original_quartic_velocity_half_radial_to_bubble_sq
      (z s) (dz s) Mz Dz hMz hDz hZ hDZ
  intro r hr
  let T : ℝ := actualRadialQuarticMomentVelocity
    ((V s r : ℂ) + z s r) ((dV s r : ℂ) + dz s r)
  let C : ℝ := actualRadialQuarticMomentVelocity
    (V s r : ℂ) (dV s r : ℂ)
  let R : ℝ := actualRadialQuarticMomentVelocity (z s r) (dz s r)
  have h1 : |T| ≤ (8 * (Mv + Mz) ^ 3 * (Dv + Dz)) * bubble r ^ 2 := hTot r hr
  have h2 : |C| ≤ (8 * Mv ^ 3 * Dv) * bubble r ^ 2 := hCore r hr
  have h3 : |R| ≤ (8 * Mz ^ 3 * Dz) * bubble r ^ 2 := hRad r hr
  have hTri1 : |T - C - R| ≤ |T - C| + |R| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (T - C) (-R)
  have hTri2 : |T - C| ≤ |T| + |C| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le T (-C)
  change |T - C - R| ≤
    (8 * ((Mv + Mz) ^ 3 * (Dv + Dz) +
      Mv ^ 3 * Dv + Mz ^ 3 * Dz)) * bubble r ^ 2
  nlinarith only [hTri1, hTri2, h1, h2, h3]

/-- The full original mixed Riesz time derivative is radius-uniform
under primitive real-core/complex-radiation half-radial velocities.
No independent derivative of the potential or adjusted source is assumed. -/
theorem actual_Hartree_mixed_Riesz_time_uniform_from_half_radial_orbit
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (r s : ℝ) (hr : 0 < r) (I : Set ℝ) (hI : I ∈ 𝓝 s)
    (hMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeMixedRieszTimeIntegrand V z r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hInt : IntegrableOn
      (actualHartreeMixedRieszTimeIntegrand V z r s) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (actualHartreeMixedRieszTimeVelocity V dV z dz r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeMixedRieszTimeVelocity V dV z dz r t rho| ≤ B rho)
    (hVDeriv : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun u => V u rho) (dV t rho) t)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun u => (z u rho).re) (dz t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun u => (z u rho).im) (dz t rho).im t)
    (Mv Mz Dv Dz : ℝ)
    (hMv : 0 ≤ Mv) (hMz : 0 ≤ Mz)
    (hDv : 0 ≤ Dv) (hDz : 0 ≤ Dz)
    (hVelOriginalMeas : Measurable
      (fun rho => actualHartreeMixedQuarticTimeVelocity V dV z dz s rho))
    (hV : ∀ rho : ℝ, 0 < rho →
      |V s rho| ≤ Mv * Real.sqrt (bubble rho))
    (hDV : ∀ rho : ℝ, 0 < rho →
      |dV s rho| ≤ Dv * Real.sqrt (bubble rho))
    (hZ : ∀ rho : ℝ, 0 < rho →
      ‖z s rho‖ ≤ Mz * Real.sqrt (bubble rho))
    (hDZ : ∀ rho : ℝ, 0 < rho →
      ‖dz s rho‖ ≤ Dz * Real.sqrt (bubble rho)) :
    HasDerivAt
      (fun t => radialHartreePotential
        (actualWholeRadiationMixedQuartic (V t) (z t)) r)
      (radialHartreePotential
        (actualHartreeMixedQuarticTimeVelocity V dV z dz s) r) s ∧
    |radialHartreePotential
      (actualHartreeMixedQuarticTimeVelocity V dV z dz s) r| ≤
      radialHartreeRowBoundConstant *
        (8 * ((Mv + Mz) ^ 3 * (Dv + Dz) +
          Mv ^ 3 * Dv + Mz ^ 3 * Dz)) := by
  have hQ :=
    actual_Hartree_original_mixed_quartic_velocity_half_radial
      V dV z dz s Mv Mz Dv Dz
      hMv hMz hDv hDz hV hDV hZ hDZ
  exact actual_Hartree_mixed_Riesz_time_derivative_uniform_from_quartic_velocity
    V dV z dz r s hr I hI hMeas hInt hVelMeas B hB hBound
    hVDeriv hRe hIm
    (8 * ((Mv + Mz) ^ 3 * (Dv + Dz) + Mv ^ 3 * Dv + Mz ^ 3 * Dz))
    (by positivity) hVelOriginalMeas hQ

end HBL.TypeIIDynamicSelection
