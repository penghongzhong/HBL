import HBL.TypeIIDynamicSelection.ActualMomentDerivativeFromFlow
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# The genuine Hartree PDE determines the physical radiation quartic moment flux

The previous strict terminal derives d/dt m0[z(t)] by dominated differentiation
of the genuine physical three-dimensional inverse-square quartic moment.
Here the real Hartree convolution potential is put back into the actual
time-evolution PDE. Its phase contribution cancels EXACTLY.

The remaining flux comes from the original complex radial Laplacian
u_rr + 2/r u_r, with NO invented local cubic or formal source order.
The analytic assumptions are primitive local C1 radiation flow plus one
integrable derivative majorant. This file does not construct that radiation
flow, derive the required uniform time-decay estimates, or solve 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_radial_quartic_velocity_add (u v w : ℂ) :
    actualRadialQuarticMomentVelocity u (v + w) =
      actualRadialQuarticMomentVelocity u v +
        actualRadialQuarticMomentVelocity u w := by
  unfold actualRadialQuarticMomentVelocity
  simp only [Complex.add_re, Complex.add_im]
  ring

/-- The genuine quartic Riesz Hartree nonlinearity is a real-valued
potential multiplied by |u|²u. Its contribution to the physical
quartic moment derivative vanishes exactly. -/
theorem actual_radial_Hartree_nonlinearity_phase_cancel
    (u : ℝ → ℂ) (r : ℝ) :
    actualRadialQuarticMomentVelocity (u r)
      (Complex.I * complexRadialHartreeNonlinearity u r) = 0 := by
  have heq :
      Complex.I * complexRadialHartreeNonlinearity u r =
        Complex.I *
          (radialHartreePotential (fun rho => ‖u rho‖ ^ 4) r : ℂ) *
          (‖u r‖ ^ 2 : ℝ) * u r := by
    unfold complexRadialHartreeNonlinearity
    ring
  rw [heq]
  exact actual_Hartree_real_potential_quartic_phase_cancellation
    (u r) (radialHartreePotential (fun rho => ‖u rho‖ ^ 4) r)

/-- The ORIGINAL energy-critical Hartree equation eliminates the
nonlinear moment source exactly, leaving only the physical radial
Laplacian flux. The PDE equality is an input about its actual jet,
not a moment-derivative hypothesis. -/
theorem actual_radial_Hartree_PDE_quartic_velocity_flux
    (u : ℝ → ℂ) (r : ℝ) (ut : ℂ)
    (hPDE : ut = Complex.I *
      (complexRadialLaplacian u r +
        complexRadialHartreeNonlinearity u r)) :
    actualRadialQuarticMomentVelocity (u r) ut =
      -4 * ‖u r‖ ^ 2 *
        ((u r).re * (complexRadialLaplacian u r).im -
          (u r).im * (complexRadialLaplacian u r).re) := by
  rw [hPDE, mul_add, actual_radial_quartic_velocity_add,
    actual_radial_Hartree_nonlinearity_phase_cancel, add_zero]
  unfold actualRadialQuarticMomentVelocity
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Genuine differentiated 3D inverse-square Hartree radiation moment
on the ORIGINAL radial equation. Neither HasDerivAt of the moment
nor a local cubic replacement is an input.

The result retains the true physical radial Laplacian, with 2/r term,
and the original quartic Riesz nonlinearity in the hypothesis, which
is then rigorously eliminated from the moment source by its real phase. -/
theorem actual_physical_threeD_Hartree_radiation_moment_PDE_flux
    (z zt : ℝ → ℝ → ℂ)
    (t₀ : ℝ) (I : Set ℝ)
    (hI : I ∈ 𝓝 t₀)
    (hZmeas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn (fun rho => ‖z t₀ rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho => actualRadialQuarticMomentVelocity (z t₀ rho) (zt t₀ rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt t₀ rho = Complex.I *
        (complexRadialLaplacian (z t₀) rho +
          complexRadialHartreeNonlinearity (z t₀) rho)) :
    HasDerivAt (fun t => actualPhysicalInverseSquareMoment (z t))
      (-16 * Real.pi * ∫ rho in Ioi (0 : ℝ),
        ‖z t₀ rho‖ ^ 2 *
          ((z t₀ rho).re * (complexRadialLaplacian (z t₀) rho).im -
            (z t₀ rho).im * (complexRadialLaplacian (z t₀) rho).re))
      t₀ := by
  have hMoment := actual_physical_threeD_moment_hasDerivAt_of_dominated_radiation
    z zt t₀ I hI hZmeas hZint hVelMeas B hB hBound hRe hIm
  have hint :
      (∫ rho in Ioi (0 : ℝ),
        actualRadialQuarticMomentVelocity (z t₀ rho) (zt t₀ rho)) =
      -4 * (∫ rho in Ioi (0 : ℝ),
        ‖z t₀ rho‖ ^ 2 *
          ((z t₀ rho).re * (complexRadialLaplacian (z t₀) rho).im -
            (z t₀ rho).im * (complexRadialLaplacian (z t₀) rho).re)) := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ), (-4) *
            (‖z t₀ rho‖ ^ 2 *
              ((z t₀ rho).re * (complexRadialLaplacian (z t₀) rho).im -
                (z t₀ rho).im * (complexRadialLaplacian (z t₀) rho).re)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro rho hrho
        have hp := actual_radial_Hartree_PDE_quartic_velocity_flux
          (z t₀) rho (zt t₀ rho) (hPDE rho hrho)
        convert hp using 1
        ring
      _ = _ := by rw [integral_const_mul]
  convert hMoment using 1
  rw [hint]
  ring

#print axioms actual_radial_Hartree_nonlinearity_phase_cancel
#print axioms actual_radial_Hartree_PDE_quartic_velocity_flux
#print axioms actual_physical_threeD_Hartree_radiation_moment_PDE_flux

end HBL.TypeIIDynamicSelection
