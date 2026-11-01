import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalPDEJets
import HBL.TypeIIDynamicSelection.ActualMixedQuarticGain
import Mathlib.Tactic

/-!
# True radial Hartree PDE: terminal real-phase and complete mixed source time jet

For the selected nonzero smooth real annular datum g, the original
radial Hartree equation makes the terminal velocity purely imaginary
at EVERY positive spatial radius, not merely inside the flat core.
Both the Laplacian and the nonlocal quartic Hartree potential are kept.

For a real fixed background V, this forces the first time derivative of
|V+z(t)|^4-|V|^4-|z(t)|^4 to vanish at the terminal time, by the real
coordinate quartic chain rule. Thus the actual entire mixed quartic
source has a genuine first temporal jet cancellation at terminal time.

This is a PDE consequence, NOT a claim of off-terminal uniform flatness
or complete manuscript one-layer 2.12 closure.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The ORIGINAL radial Hartree vector field is purely imaginary at
any smooth REAL profile. No fictitious local cubic replaces the
full quartic Riesz convolution. -/
theorem actual_real_smooth_radial_Hartree_rhs_real_zero
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {r : ℝ} (hr : 0 < r) :
    (Complex.I *
      (complexRadialLaplacian (fun x => (g x : ℂ)) r +
        complexRadialHartreeNonlinearity (fun x => (g x : ℂ)) r)).re = 0 := by
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x := by
    intro x _
    exact hg.differentiable (by norm_num) x
  have hgdiff : ContDiff ℝ ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hdiff2 : DifferentiableAt ℝ (deriv g) r :=
    hgdiff.differentiable (by norm_num) r
  rw [complexRadialLaplacian_ofReal g hdiff hr hdiff2,
    complexRadialHartreeNonlinearity_ofReal g r]
  simp

/-- In the actual regular Hartree PDE, the specified real terminal datum
has zero real velocity at EVERY positive radius. Unlike the old core-only
jet this statement retains the full nonlocal Hartree PDE globally. -/
theorem actual_one_orbit_Hartree_terminal_real_velocity_zero
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hr : 0 < r) :
    (zt T r).re = 0 := by
  rw [hPDE r hr, hTerminal]
  exact actual_real_smooth_radial_Hartree_rhs_real_zero
    actualOneOrbitTerminalBump actual_one_orbit_terminal_bump_smooth hr

/-- Elementary nonlinear quartic cancellation for a real background
and a real terminal value with purely imaginary velocity.
All three actual physical density terms are retained. -/
theorem actual_real_terminal_full_mixed_quartic_first_jet_zero
    (V : ℝ) (z : ℝ → ℂ) (dz : ℂ) (T : ℝ)
    (hzIm : (z T).im = 0)
    (hdzRe : dz.re = 0)
    (hRe : HasDerivAt (fun t => (z t).re) dz.re T)
    (hIm : HasDerivAt (fun t => (z t).im) dz.im T) :
    HasDerivAt
      (fun t => ‖(V : ℂ) + z t‖ ^ 4 -
        ‖(V : ℂ)‖ ^ 4 - ‖z t‖ ^ 4)
      0 T := by
  have hReFull : HasDerivAt
      (fun t => ((V : ℂ) + z t).re) dz.re T := by
    convert ((hasDerivAt_const T V).add hRe) using 1; simp
  have hImFull : HasDerivAt
      (fun t => ((V : ℂ) + z t).im) dz.im T := by
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hIm
  have hFull := actual_radial_quartic_hasDerivAt
    (fun t => (V : ℂ) + z t) dz T hReFull hImFull
  have hZ := actual_radial_quartic_hasDerivAt
    z dz T hRe hIm
  have hVFull :
      actualRadialQuarticMomentVelocity ((V : ℂ) + z T) dz = 0 := by
    simp [actualRadialQuarticMomentVelocity, hzIm, hdzRe]
  have hVZ :
      actualRadialQuarticMomentVelocity (z T) dz = 0 := by
    simp [actualRadialQuarticMomentVelocity, hzIm, hdzRe]
  have hConst : HasDerivAt (fun _ : ℝ => ‖(V : ℂ)‖ ^ 4) 0 T :=
    hasDerivAt_const T _
  have hMixed := (hFull.sub hConst).sub hZ
  rw [hVFull, hVZ] at hMixed
  change HasDerivAt
    (fun t => ‖(V : ℂ) + z t‖ ^ 4 -
      ‖(V : ℂ)‖ ^ 4 - ‖z t‖ ^ 4)
    (0 - 0 - 0) T at hMixed
  simpa only [sub_zero] using hMixed

/-- The complete real-linear/quadratic/cubic Hartree mixed density
has zero FIRST TIME JET at the selected terminal datum along the
REAL original radial Hartree PDE (at fixed real background V).
This does NOT assume the derivative of the mixed density. -/
theorem actual_one_orbit_Hartree_terminal_full_mixed_quartic_time_jet_zero
    (z zt : ℝ → ℝ → ℂ) (T V : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ r : ℝ, 0 < r →
      zt T r = Complex.I *
        (complexRadialLaplacian (z T) r +
          complexRadialHartreeNonlinearity (z T) r))
    {r : ℝ} (hr : 0 < r)
    (hRe : HasDerivAt (fun t => (z t r).re) (zt T r).re T)
    (hIm : HasDerivAt (fun t => (z t r).im) (zt T r).im T) :
    HasDerivAt
      (fun t => ‖(V : ℂ) + z t r‖ ^ 4 -
        ‖(V : ℂ)‖ ^ 4 - ‖z t r‖ ^ 4)
      0 T := by
  have hzIm : (z T r).im = 0 := by
    rw [hTerminal]
    simp [actualOneOrbitTerminalRadiation]
  exact actual_real_terminal_full_mixed_quartic_first_jet_zero
    V (fun t => z t r) (zt T r) T hzIm
    (actual_one_orbit_Hartree_terminal_real_velocity_zero
      z zt T hTerminal hPDE hr) hRe hIm

end HBL.TypeIIDynamicSelection
