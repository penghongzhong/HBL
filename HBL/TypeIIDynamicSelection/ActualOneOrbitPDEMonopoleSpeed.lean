import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalPDEJets
import HBL.TypeIIDynamicSelection.ActualMomentProfileDynamics
import Mathlib.Tactic

/-!
# Original Hartree PDE enforces the terminal slow monopole drift

For the specific nonzero real annular radiation chosen for the ONE-ORBIT
construction, the genuine 3D inverse-square Hartree quartic moment has
vanishing first physical-time derivative at the terminal data. This is
already derived from the true radial Hartree equation and an explicit
dominated-differentiation regularity boundary.

Combining that fact with the verified physical modulation clock,
  ell_s=-b ell,  t_s=ell^2,
gives c_s=-b c AT THE TERMINAL SLICE, for the genuine coefficient
  c= kappa_H ell m0[z(t)].
The full moving monopole time jet then contains ONLY -b c times the
exact derivative of the physical cutoff profile. No prescribed
Type-II rate, radiation source mass, or new axiom is introduced.

This is not an assertion that the terminal flatness persists for all
earlier times or that original manuscript 2.12 is closed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail HBL.Modulation.Monopole

/-- Physical Hartree PDE makes the selected quartic moment stationary
to first order at the real terminal datum. The exact physical clock
then forces c_s=-b c without any assumed terminal exponent. -/
theorem actual_one_orbit_terminal_Hartree_monopole_speed_from_PDE
    (ell b time : ℝ → ℝ) (z zt : ℝ → ℝ → ℂ)
    {s : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hTerminal : z (time s) = actualOneOrbitTerminalRadiation)
    (I : Set ℝ) (hI : I ∈ 𝓝 (time s))
    (hZmeas : ∀ᶠ t in 𝓝 (time s),
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn (fun rho => ‖z (time s) rho‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho => actualRadialQuarticMomentVelocity
        (z (time s) rho) (zt (time s) rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt (time s) rho = Complex.I *
        (complexRadialLaplacian (z (time s)) rho +
          complexRadialHartreeNonlinearity (z (time s)) rho)) :
    HasDerivAt (actualPhysicalRadiationMonopole ell z time)
      (-(b s * actualPhysicalRadiationMonopole ell z time s)) s := by
  have hMomentZero :=
    actual_one_orbit_terminal_Hartree_physical_moment_deriv_zero
      z zt (time s) hTerminal I hI hZmeas hZint hVelMeas
      B hB hBound hRe hIm hPDE
  have hc :=
    actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
      ell b z time hEll hEllPos hTime hMomentZero
  simpa only [mul_zero, add_zero] using hc

/-- The actual full (moving-cutoff included) monopole profile has
a dynamically derived first time jet on the selected Hartree terminal
slice. This is not a stationary-cutoff approximation. -/
theorem actual_one_orbit_terminal_Hartree_monopole_profile_jet_from_PDE
    (ell b time : ℝ → ℝ) (z zt : ℝ → ℝ → ℂ)
    {s : ℝ} (r : ℝ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hTerminal : z (time s) = actualOneOrbitTerminalRadiation)
    (I : Set ℝ) (hI : I ∈ 𝓝 (time s))
    (hZmeas : ∀ᶠ t in 𝓝 (time s),
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn (fun rho => ‖z (time s) rho‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho => actualRadialQuarticMomentVelocity
        (z (time s) rho) (zt (time s) rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt (time s) rho = Complex.I *
        (complexRadialLaplacian (z (time s)) rho +
          complexRadialHartreeNonlinearity (z (time s)) rho)) :
    HasDerivAt
      (fun t => actualMomentMonopoleProfile ell z time t r)
      (-(b s * actualPhysicalRadiationMonopole ell z time s) *
        monopoleRadialProfile r *
        (1 -
          cutoff (actualPhysicalRadiationMonopole ell z time s * r / 4) -
          (actualPhysicalRadiationMonopole ell z time s * r / 4) *
            deriv cutoff
              (actualPhysicalRadiationMonopole ell z time s * r / 4))) s := by
  have hMomentZero :=
    actual_one_orbit_terminal_Hartree_physical_moment_deriv_zero
      z zt (time s) hTerminal I hI hZmeas hZint hVelMeas
      B hB hBound hRe hIm hPDE
  have hp :=
    actual_moment_monopole_profile_threeD_hasDerivAt
      ell b z time r hEll hEllPos hTime hMomentZero
  simpa only [mul_zero, add_zero] using hp

end HBL.TypeIIDynamicSelection
