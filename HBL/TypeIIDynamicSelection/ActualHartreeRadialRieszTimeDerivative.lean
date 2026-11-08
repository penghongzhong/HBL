import HBL.TypeIIDynamicSelection.ActualMomentDerivativeFromFlow
import HBL.RadialHartreePotential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
# Time derivative of the GENUINE radial inverse-square Hartree Riesz potential

The source is not an abstract local replacement:
  I[|z(s)|^4](r) = (2*pi*kappa/r)
       * ∫_{0<rho} rho*log((r+rho)/|r-rho|)*|z(s,rho)|^4 drho.

The time derivative of the integrand comes from the previously verified
actual complex radial quartic derivative, with both real and imaginary
channels and including zero radiation. We then differentiate the original
nonlocal logarithmic Riesz integral via Mathlib's genuine dominated
parametric integral theorem. The derivative of the Riesz potential
itself is NOT a premise.

The time derivative is taken at FIXED positive observation radius r.
Differentiating the spatial observation point r(s), the moving Kummer
fundamental pair and the complete quartic Hartree interaction remain
separate and indispensable in the full Type-II profile proof.

Inputs are original radiation pointwise C1 along the orbit and one
explicit integrable majorant of the actual logarithmic-kernel weighted
quartic velocity. This is not a rate hypothesis and introduces no
extra axiom or artificial forcing.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Genuine physical radial logarithmic Riesz density at a fixed observer. -/
def actualHartreeRieszQuarticTimeIntegrand
    (z : ℝ → ℝ → ℂ) (r t rho : ℝ) : ℝ :=
  rho * hartreeRadialLog r rho * ‖z t rho‖ ^ 4

/-- Differentiated physical radial logarithmic density from actual z and z_s. -/
def actualHartreeRieszQuarticTimeVelocity
    (z dz : ℝ → ℝ → ℂ) (r t rho : ℝ) : ℝ :=
  rho * hartreeRadialLog r rho *
    actualRadialQuarticMomentVelocity (z t rho) (dz t rho)

/-- Under one genuine integrable Riesz velocity envelope, the original
radial Hartree potential has a computed time derivative. This is NOT a
hypothesis about the differentiated Hartree potential. -/
theorem actual_Hartree_radial_Riesz_potential_time_derivative_from_radiation
    (z dz : ℝ → ℝ → ℂ) (r s : ℝ) (_hr : 0 < r)
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
      HasDerivAt (fun x : ℝ => (z x rho).re) (dz t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).im) (dz t rho).im t) :
    HasDerivAt
      (fun t => radialHartreePotential (fun rho => ‖z t rho‖ ^ 4) r)
      ((2 * Real.pi * hartreeKappa / r) *
        ∫ rho in Ioi (0 : ℝ),
          actualHartreeRieszQuarticTimeVelocity z dz r s rho) s := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ :=
    fun t rho => actualHartreeRieszQuarticTimeIntegrand z r t rho
  let F' : ℝ → ℝ → ℝ :=
    fun t rho => actualHartreeRieszQuarticTimeVelocity z dz r t rho
  have hbd : ∀ᵐ rho ∂μ, ∀ t ∈ I, ‖F' t rho‖ ≤ B rho := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    intro t ht
    simpa only [F', Real.norm_eq_abs] using hBound rho hrho t ht
  have hderiv : ∀ᵐ rho ∂μ, ∀ t ∈ I,
      HasDerivAt (F · rho) (F' t rho) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    intro t ht
    have hQuartic := actual_radial_quartic_hasDerivAt
      (fun x => z x rho) (dz t rho) t
      (hRe rho hrho t ht) (hIm rho hrho t ht)
    have hd := hQuartic.const_mul (rho * hartreeRadialLog r rho)
    simpa only [F, F',
      actualHartreeRieszQuarticTimeIntegrand,
      actualHartreeRieszQuarticTimeVelocity] using hd
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := μ) (s := I) (x₀ := s)
    (bound := B) hI hZmeas hZint hVelMeas hbd hB hderiv
  simpa only [radialHartreePotential,
    actualHartreeRieszQuarticTimeIntegrand,
    actualHartreeRieszQuarticTimeVelocity, F, F'] using
    hresult.2.const_mul (2 * Real.pi * hartreeKappa / r)

end HBL.TypeIIDynamicSelection
