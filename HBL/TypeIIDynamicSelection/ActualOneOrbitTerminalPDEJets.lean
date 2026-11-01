import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalRadiation
import HBL.TypeIIDynamicSelection.ActualMomentTransportGain
import Mathlib.Tactic

/-!
# Genuine Hartree PDE terminal jets for a selected real annular radiation

The fixed terminal radiation g(r)=chi(4r)(1-chi(r/2)) is smooth,
real-valued and vanishes for r<=1/4. Its true 3D inverse-square
quartic moment is strictly positive by the preceding accepted theorem.

A REAL terminal datum gives zero first derivative of that moment,
because the exact radial Laplacian has real coefficients and the
full Hartree Riesz potential is also real. This is an actual PDE
cancellation, not a prescribed limit or a postulated source.

Furthermore the original radial Hartree PDE forces the first time jet
to vanish on the positive core 0<r<1/4. This is an actual flatness
property needed for the one-layer radiation source mechanism.
No high-order time-jet, uniform Kummer matching, or Type II orbit is
claimed; the relevant PDE regularity is explicit below.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Any real infinitely differentiable radial profile has ZERO
imaginary physical 3D Hartree moment flux at its initial time.
The full positive-radius radial Laplacian is used, not a free or
local surrogate for the Hartree nonlinear source. -/
theorem actual_real_smooth_radial_Hartree_moment_flux_zero
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    actualMomentLaplacianFlux (fun r => (g r : ℂ)) = 0 := by
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x := by
    intro x _
    exact hg.differentiable (by norm_num) x
  have hgdiff : ContDiff ℝ ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hdiff2 : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (deriv g) x := by
    intro x _
    exact hgdiff.differentiable (by norm_num) x
  have hpoint (r : ℝ) (hr : 0 < r) :
      ‖(g r : ℂ)‖ ^ 2 *
        ((g r : ℂ).re *
          (complexRadialLaplacian (fun x => (g x : ℂ)) r).im -
         (g r : ℂ).im *
          (complexRadialLaplacian (fun x => (g x : ℂ)) r).re) = 0 := by
    have hLap := complexRadialLaplacian_ofReal g hdiff hr (hdiff2 r hr)
    rw [hLap]
    simp
  have heq :
      (fun r : ℝ =>
        ‖(g r : ℂ)‖ ^ 2 *
          ((g r : ℂ).re *
            (complexRadialLaplacian (fun x => (g x : ℂ)) r).im -
           (g r : ℂ).im *
            (complexRadialLaplacian (fun x => (g x : ℂ)) r).re))
      =ᵐ[(volume : Measure ℝ).restrict (Ioi (0 : ℝ))]
        (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hpoint r hr
  unfold actualMomentLaplacianFlux
  rw [integral_congr_ae heq]
  simp

/-- The original selected, explicitly nonzero terminal radiation has
vanishing physical Laplacian moment flux, with no additional condition. -/
theorem actual_one_orbit_terminal_Hartree_moment_flux_zero :
    actualMomentLaplacianFlux actualOneOrbitTerminalRadiation = 0 := by
  exact actual_real_smooth_radial_Hartree_moment_flux_zero
    actualOneOrbitTerminalBump actual_one_orbit_terminal_bump_smooth

/-- The actual radial Hartree PDE has ZERO first time jet throughout
the original flat positive-radius core at the terminal time.
The full quartic Riesz nonlinearity is retained and vanishes because
its local |z|²z factor is zero there. -/
theorem actual_one_orbit_terminal_Hartree_core_velocity_zero
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hrpos : 0 < r) (hrcore : r < 1 / 4) :
    zt T r = 0 := by
  have hzero (x : ℝ) (hx : x < 1 / 4) : z T x = 0 := by
    rw [hTerminal]
    have hb := actual_one_orbit_terminal_bump_zero_core
      (r := x) (le_of_lt hx)
    simp [actualOneOrbitTerminalRadiation, hb]
  have hD1 (x : ℝ) (hx : x < 1 / 4) :
      deriv (z T) x = 0 := by
    have he : (z T) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact hzero y hy
    rw [he.deriv_eq]
    exact deriv_const x 0
  have hD2 : deriv (deriv (z T)) r = 0 := by
    have he : deriv (z T) =ᶠ[𝓝 r]
        (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hrcore] with y hy
      exact hD1 y hy
    rw [he.deriv_eq]
    exact deriv_const r 0
  have hLap : complexRadialLaplacian (z T) r = 0 := by
    simp [complexRadialLaplacian, hD1 r hrcore, hD2]
  have hNL : complexRadialHartreeNonlinearity (z T) r = 0 := by
    simp [complexRadialHartreeNonlinearity, hzero r hrcore]
  simpa only [hLap, hNL, add_zero, mul_zero] using hPDE r hrpos

/-- The SAME first radial-core time jet vanishes on the actual
strong Hartree flow, not merely on its velocity field. -/
theorem actual_one_orbit_terminal_Hartree_core_time_derivative_zero
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hrpos : 0 < r) (hrcore : r < 1 / 4)
    (hTime : HasDerivAt (fun t => z t r) (zt T r) T) :
    HasDerivAt (fun t => z t r) 0 T := by
  have hzero := actual_one_orbit_terminal_Hartree_core_velocity_zero
    z zt T hTerminal hPDE hrpos hrcore
  simpa only [hzero] using hTime

/-- Strict physical quartic-moment derivative cancellation at the
explicit real terminal datum for the genuine radial Hartree PDE.
No separate scalar moment derivative is assumed. -/
theorem actual_one_orbit_terminal_Hartree_physical_moment_deriv_zero
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (I : Set ℝ) (hI : I ∈ 𝓝 T)
    (hZmeas : ∀ᶠ t in 𝓝 T,
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn (fun rho => ‖z T rho‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho => actualRadialQuarticMomentVelocity (z T rho) (zt T rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho)) :
    HasDerivAt (fun t => actualPhysicalInverseSquareMoment (z t))
      0 T := by
  have hPDEFlux := actual_physical_threeD_Hartree_radiation_moment_PDE_flux
    z zt T I hI hZmeas hZint hVelMeas B hB hBound hRe hIm hPDE
  have hFlux : actualMomentLaplacianFlux (z T) = 0 := by
    rw [hTerminal]
    exact actual_one_orbit_terminal_Hartree_moment_flux_zero
  simpa only [actualMomentLaplacianFlux, hFlux] using hPDEFlux

end HBL.TypeIIDynamicSelection
