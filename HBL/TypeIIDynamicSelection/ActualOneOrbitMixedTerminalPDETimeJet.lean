import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalPDEJets
import HBL.TypeIIDynamicSelection.ActualOneOrbitMovingMonopoleMixed
import Mathlib.Tactic

/-!
# Actual physical Hartree PDE: first time jet of the FULL mixed quartic source

For the explicitly nonzero real annular terminal radiation, the
ORIGINAL radial Hartree PDE forces its terminal time velocity to be
pure imaginary at EVERY positive radius. Both the genuine radial
Laplacian and the nonlocal quartic Hartree potential are retained.

Consequently the true mixed quartic source around the frozen
moment-generated monopole V_c has zero first time derivative
at this terminal instant, assuming only the pointwise C1 regularity
provided by the standard high-regularity Hartree local-flow boundary.

This is a mathematically real PDE time jet and not an abstract
source-order marker. It does NOT establish a uniform moving-annulus
off-terminal tail, or the entire original manuscript one-layer
Fredholm/Kummer/remote solve, so original 2.12 remains open.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The real part of the actual Hartree PDE time velocity vanishes
for the selected smooth REAL terminal radiation at every positive
radius, without assuming the velocity to be imaginary. -/
theorem actual_one_orbit_terminal_Hartree_PDE_velocity_real_zero
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hr : 0 < r) :
    (zt T r).re = 0 := by
  have hg := actual_one_orbit_terminal_bump_smooth
  have hdiff : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ actualOneOrbitTerminalBump x := by
    intro x _
    exact hg.differentiable (by norm_num) x
  have hgdiff : ContDiff ℝ ∞ (deriv actualOneOrbitTerminalBump) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hdiff2 : DifferentiableAt ℝ
      (deriv actualOneOrbitTerminalBump) r :=
    hgdiff.differentiable (by norm_num) r
  have hLaplacian :
      complexRadialLaplacian (z T) r =
        (radialLaplacian actualOneOrbitTerminalBump r : ℂ) := by
    rw [hTerminal]
    exact complexRadialLaplacian_ofReal
      actualOneOrbitTerminalBump hdiff hr hdiff2
  have hNonlocal :
      complexRadialHartreeNonlinearity (z T) r =
        (radialHartreeNonlinearity actualOneOrbitTerminalBump r : ℂ) := by
    rw [hTerminal]
    exact complexRadialHartreeNonlinearity_ofReal
      actualOneOrbitTerminalBump r
  rw [hPDE r hr, hLaplacian, hNonlocal]
  simp

/-- The genuine pointwise quartic-moment density has zero time
velocity at the explicit real Hartree terminal datum. -/
theorem actual_one_orbit_terminal_Hartree_PDE_quartic_velocity_zero
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hr : 0 < r) :
    actualRadialQuarticMomentVelocity (z T r) (zt T r) = 0 := by
  have hRe :=
    actual_one_orbit_terminal_Hartree_PDE_velocity_real_zero
      z zt T hTerminal hPDE hr
  have hIm : (z T r).im = 0 := by
    rw [hTerminal]
    simp [actualOneOrbitTerminalRadiation]
  simp [actualRadialQuarticMomentVelocity, hRe, hIm]

/-- The complete physical quartic mixed-source instantaneous time
velocity around the fixed TRUE moment-generated V_c also vanishes:
no linear-only approximation or local-cubic replacement. -/
theorem actual_one_orbit_terminal_Hartree_PDE_full_mixed_velocity_zero
    (ell : ℝ) (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hr : 0 < r) :
    actualRadialQuarticMomentVelocity
        (((actualOneOrbitMovingMonopole ell r : ℝ) : ℂ) + z T r)
        (zt T r) -
      actualRadialQuarticMomentVelocity (z T r) (zt T r) = 0 := by
  have hRe :=
    actual_one_orbit_terminal_Hartree_PDE_velocity_real_zero
      z zt T hTerminal hPDE hr
  have hIm : (z T r).im = 0 := by
    rw [hTerminal]
    simp [actualOneOrbitTerminalRadiation]
  simp [actualRadialQuarticMomentVelocity, hRe, hIm]

/-- For an actual C1 Hartree terminal trajectory, the full mixed
quartic density, with the physical V_c held at its terminal value,
has ZERO first time derivative, derived from the ORIGINAL PDE. -/
theorem actual_one_orbit_terminal_Hartree_PDE_full_mixed_time_derivative_zero
    (ell : ℝ) (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hr : 0 < r)
    (hRe : HasDerivAt (fun t : ℝ => (z t r).re) (zt T r).re T)
    (hIm : HasDerivAt (fun t : ℝ => (z t r).im) (zt T r).im T) :
    HasDerivAt
      (fun t : ℝ =>
        ‖((actualOneOrbitMovingMonopole ell r : ℝ) : ℂ) + z t r‖ ^ 4 -
          ‖((actualOneOrbitMovingMonopole ell r : ℝ) : ℂ)‖ ^ 4 -
            ‖z t r‖ ^ 4) 0 T := by
  let V : ℝ := actualOneOrbitMovingMonopole ell r
  have hReSum : HasDerivAt
      (fun t : ℝ => (((V : ℝ) : ℂ) + z t r).re) (zt T r).re T := by
    simpa only [Complex.add_re, Complex.ofReal_re, zero_add] using
      ((hasDerivAt_const T V).add hRe)
  have hImSum : HasDerivAt
      (fun t : ℝ => (((V : ℝ) : ℂ) + z t r).im) (zt T r).im T := by
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hIm
  have hPlus := actual_radial_quartic_hasDerivAt
    (fun t : ℝ => ((V : ℝ) : ℂ) + z t r)
      (zt T r) T hReSum hImSum
  have hConst := hasDerivAt_const T (‖((V : ℝ) : ℂ)‖ ^ 4)
  have hRad := actual_radial_quartic_hasDerivAt
    (fun t : ℝ => z t r) (zt T r) T hRe hIm
  have hVelocity := actual_one_orbit_terminal_Hartree_PDE_full_mixed_velocity_zero
    ell z zt T hTerminal hPDE hr
  have hDerivative := (hPlus.sub hConst).sub hRad
  simpa only [sub_zero, hVelocity] using hDerivative

end HBL.TypeIIDynamicSelection
