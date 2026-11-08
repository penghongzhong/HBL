import HBL.TypeIIDynamicSelection.ActualHartreeTwoStageCoreTimeTangent
import HBL.TypeIIDynamicSelection.ActualHartreeTwoStageRadiationTimeTangent
import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceTimeFromPhysicalScaledOrbit
import Mathlib.Tactic

/-!
# ORIGINAL Hartree fixed-Kummer scaled core and radiation: produced time tangents

The 3D quartic Hartree original three-Riesz source producer requires
time derivatives of the REAL monopole V_a,c and the COMPLEX radiation
Z_a,ell. This module provides those derivatives directly from primitive
physical a(t),c(t),ell(t) and the one actual full C1 radiation map
(t,rho) -> z(t,rho), rather than assuming differentiability of the
critically scaled sources independently.

The two-stage critical scaling includes BOTH square-root amplitude factors,
both moving radial arguments, the moving amplitude-dependent monopole
cutoff (including c=0), and the real/imag radiation time channels.

The only inputs are actual physical parameter derivatives and a C1
differential for the original complex radiation; genuine Riesz dominated
kernel integrals remain separate explicitly visible analytic obligations.
No Type-II blowup rate or full PDE residual is assumed.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeTwoStageRealCoreTimeVelocity
    (a c adot cdot : ℝ → ℝ) (s r : ℝ) : ℝ :=
  (adot s / (2 * Real.sqrt (a s))) *
      actualMomentLockedCore (c s) (a s * r) +
    Real.sqrt (a s) *
      actualMomentLockedCoreTotalTangent
        (c s) (a s * r) (cdot s) (adot s * r)

def actualHartreeTwoStageComplexRadiationTimeVelocity
    (a ell adot ellDot : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (Dz : ℝ → ℝ → (ℝ × ℝ →L[ℝ] ℂ)) (s r : ℝ) : ℂ :=
  (((adot s / (2 * Real.sqrt (a s)) : ℝ) : ℂ)) *
      (Real.sqrt (ell s) : ℂ) * z s (ell s * (a s * r)) +
    (Real.sqrt (a s) : ℂ) *
      (((ellDot s / (2 * Real.sqrt (ell s)) : ℝ) : ℂ)) *
      z s (ell s * (a s * r)) +
    (Real.sqrt (a s) : ℂ) * (Real.sqrt (ell s) : ℂ) *
      Dz s r (1, ellDot s * (a s * r) + ell s * (adot s * r))

/-- Full true two-stage core and complex radiation time tangents at all
positive physical radii on one time set. Source-time regularity is
DERIVED from its primitive physical data, not inserted as a new packet. -/
theorem actual_Hartree_one_orbit_scaled_core_and_radiation_tangents
    (a ell c adot ellDot cdot : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ)
    (Dz : ℝ → ℝ → (ℝ × ℝ →L[ℝ] ℂ))
    (I : Set ℝ)
    (hA : ∀ s ∈ I, HasDerivAt a (adot s) s)
    (hEll : ∀ s ∈ I, HasDerivAt ell (ellDot s) s)
    (hc : ∀ s ∈ I, HasDerivAt c (cdot s) s)
    (ha : ∀ s ∈ I, 0 < a s)
    (hEllPos : ∀ s ∈ I, 0 < ell s)
    (hZ : ∀ s ∈ I, ∀ r : ℝ, 0 < r →
      HasFDerivAt (fun p : ℝ × ℝ => z p.1 p.2)
        (Dz s r) (s, ell s * (a s * r))) :
    (∀ r : ℝ, 0 < r → ∀ s ∈ I,
      HasDerivAt
        (fun t => actualHartreeTrueTwoStageScaledCore a c t r)
        (actualHartreeTwoStageRealCoreTimeVelocity
          a c adot cdot s r) s) ∧
    (∀ r : ℝ, 0 < r → ∀ s ∈ I,
      HasDerivAt
        (fun t => actualHartreeTrueTwoStageScaledRadiation
          a ell z t r)
        (actualHartreeTwoStageComplexRadiationTimeVelocity
          a ell adot ellDot z Dz s r) s) := by
  constructor
  · intro r hr s hs
    have h := actual_Hartree_two_stage_critical_core_time_hasDerivAt
      a c s r (adot s) (cdot s)
      (hA s hs) (hc s hs) (ha s hs) hr
    simpa only [actualHartreeTrueTwoStageScaledCore,
      actualMomentLockedCore,
      actualHartreeTwoStageRealCoreTimeVelocity] using h
  · intro r hr s hs
    have h := actual_Hartree_two_stage_critical_radiation_time_hasDerivAt
      a ell z s r (adot s) (ellDot s)
      (hA s hs) (hEll s hs) (ha s hs) (hEllPos s hs)
      (Dz s r) (hZ s hs r hr)
    simpa only [actualHartreeTrueTwoStageScaledRadiation,
      actualHartreeTwoStageComplexRadiationTimeVelocity] using h

end HBL.TypeIIDynamicSelection
