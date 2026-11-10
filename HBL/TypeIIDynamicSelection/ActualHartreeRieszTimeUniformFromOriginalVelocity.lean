import HBL.TypeIIDynamicSelection.ActualHartreeFullInteractionTimeFromOrbit
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Quantitative time differentiation of the actual radial Riesz rows

A derivative of the three-dimensional inverse-square Hartree potential
is not assumed: it is furnished by the existing original logarithmic
Riesz dominated-differentiation theorems for the actual quartic velocity.
The new conclusion is uniform in the positive observation radius, using
the proved original radial Riesz row and the ORIGINAL velocity densities.

The physical density-velocity condition
  |partial_t |u|^4| <= M * bubble^2
(or its mixed-polarized counterpart) is an explicit remaining orbit
estimate. In particular the theorem does NOT infer this condition merely
from C1 regularity or from an undifferentiated source envelope.
It gives no prespecified temporal rate, packet or II-type blowup.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Uniform original Riesz-potential time derivative for actual quartic
radiation: the velocity is the computed polarisation of the SAME field,
and the row constant does not depend on the observation radius. -/
theorem actual_Hartree_radial_Riesz_time_derivative_uniform_from_quartic_velocity
    (z dz : ℝ → ℝ → ℂ) (r s : ℝ) (hr : 0 < r)
    (I : Set ℝ) (hI : I ∈ 𝓝 s)
    (hZmeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand z r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand z r s) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity z dz r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity z dz r t rho| ≤ B rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun t => (z t rho).re) (dz t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun t => (z t rho).im) (dz t rho).im t)
    (M : ℝ) (hM : 0 ≤ M)
    (hVelOriginalMeas : Measurable
      (fun rho => actualRadialQuarticMomentVelocity (z s rho) (dz s rho)))
    (hVelOriginal : ∀ rho : ℝ, 0 < rho →
      |actualRadialQuarticMomentVelocity (z s rho) (dz s rho)| ≤
        M * bubble rho ^ 2) :
    HasDerivAt
      (fun t => radialHartreePotential (fun rho => ‖z t rho‖ ^ 4) r)
      (radialHartreePotential
        (fun rho => actualRadialQuarticMomentVelocity
          (z s rho) (dz s rho)) r) s ∧
    |radialHartreePotential
      (fun rho => actualRadialQuarticMomentVelocity
        (z s rho) (dz s rho)) r| ≤ radialHartreeRowBoundConstant * M := by
  have hDeriv :=
    actual_Hartree_radial_Riesz_potential_time_derivative_from_radiation
      z dz r s hr I hI hZmeas hZint hVelMeas B hB hBound hRe hIm
  have hRow :=
    radialHartreePotential_bubble_sq_domination
      (fun rho => actualRadialQuarticMomentVelocity
        (z s rho) (dz s rho)) hVelOriginalMeas hM hVelOriginal hr
  constructor
  · simpa only [radialHartreePotential,
      actualHartreeRieszQuarticTimeVelocity] using hDeriv
  · exact hRow.2

/-- The MIXED original Riesz velocity is the genuine quartic
polarisation of the real core and complex radiation, not a surrogate
density. Its time derivative is likewise uniformly bounded in radius. -/
theorem actual_Hartree_mixed_Riesz_time_derivative_uniform_from_quartic_velocity
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
    (hV : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun t => V t rho) (dV t rho) t)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun t => (z t rho).re) (dz t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun t => (z t rho).im) (dz t rho).im t)
    (M : ℝ) (hM : 0 ≤ M)
    (hVelOriginalMeas : Measurable
      (fun rho => actualHartreeMixedQuarticTimeVelocity V dV z dz s rho))
    (hVelOriginal : ∀ rho : ℝ, 0 < rho →
      |actualHartreeMixedQuarticTimeVelocity V dV z dz s rho| ≤
        M * bubble rho ^ 2) :
    HasDerivAt
      (fun t => radialHartreePotential
        (actualWholeRadiationMixedQuartic (V t) (z t)) r)
      (radialHartreePotential
        (actualHartreeMixedQuarticTimeVelocity V dV z dz s) r) s ∧
    |radialHartreePotential
      (actualHartreeMixedQuarticTimeVelocity V dV z dz s) r| ≤
        radialHartreeRowBoundConstant * M := by
  have hDeriv :=
    actual_Hartree_mixed_Riesz_potential_time_derivative_from_orbit
      V dV z dz r s hr I hI
      hMeas hInt hVelMeas B hB hBound hV hRe hIm
  have hRow :=
    radialHartreePotential_bubble_sq_domination
      (actualHartreeMixedQuarticTimeVelocity V dV z dz s)
      hVelOriginalMeas hM hVelOriginal hr
  constructor
  · simpa only [radialHartreePotential,
      actualHartreeMixedRieszTimeVelocity] using hDeriv
  · exact hRow.2

end HBL.TypeIIDynamicSelection
