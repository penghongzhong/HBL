import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalPDEJets
import Mathlib.Tactic

/-!
# Second physical Hartree time jet on the flat terminal core

For the selected real annular terminal datum, the original radial
Hartree equation forces z(T,r)=z_t(T,r)=0 on 0<r<1/4. Its *true*
inverse-square nonlocal potential need not vanish at the core, but the
pointwise cubic factor |z|² z and its first time derivative DO vanish
there. Under explicit classical mixed spatial/time differentiability
of the genuine Hartree flow, the second time jet therefore vanishes.

This is one additional PDE-derived flatness step toward 2.12. The
exchange of temporal and radial derivatives and potential time
differentiability are visible analytic conditions, not axioms, and
no full Type II orbit is claimed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual complex local cubic factor |u|²u has zero time
derivative whenever u vanishes, with no assumption on its derivative. -/
theorem actual_complex_local_cubic_time_derivative_zero
    (u : ℝ → ℂ) (T : ℝ) (du : ℂ)
    (hU : HasDerivAt u du T)
    (hRe : HasDerivAt (fun t => (u t).re) du.re T)
    (hIm : HasDerivAt (fun t => (u t).im) du.im T)
    (hZero : u T = 0) :
    HasDerivAt
      (fun t => ((‖u t‖ ^ 2 : ℝ) : ℂ) * u t) 0 T := by
  have hSqReal :
      HasDerivAt (fun t => ‖u t‖ ^ 2)
        (2 * (u T).re * du.re + 2 * (u T).im * du.im) T := by
    have hh := (hRe.pow 2).add (hIm.pow 2)
    convert hh using 1
    · funext t
      calc
        ‖u t‖ ^ 2 = Complex.normSq (u t) := by
          rw [Complex.normSq_eq_norm_sq]
        _ = (u t).re ^ 2 + (u t).im ^ 2 := by
          rw [Complex.normSq_apply]
    · ring
  have hSq : HasDerivAt (fun t => ‖u t‖ ^ 2) 0 T := by
    simpa only [hZero, Complex.zero_re, Complex.zero_im,
      zero_mul, mul_zero, add_zero] using hSqReal
  have hc := hSq.ofReal_comp.mul hU
  convert hc using 1
  · rfl
  · simp [hZero]

/-- The genuine radial nonlocal Hartree term, not a local-cubic
surrogate, has zero first time derivative at any spatial point
where the physical complex field vanishes. The nonlocal potential
is allowed to be nonzero. -/
theorem actual_Hartree_nonlocal_time_derivative_zero_at_core
    (z : ℝ → ℝ → ℂ) (T r : ℝ) (dz : ℂ) (pDot : ℝ)
    (hU : HasDerivAt (fun t => z t r) dz T)
    (hRe : HasDerivAt (fun t => (z t r).re) dz.re T)
    (hIm : HasDerivAt (fun t => (z t r).im) dz.im T)
    (hZero : z T r = 0)
    (hPotential : HasDerivAt
      (fun t => radialHartreePotential
        (fun rho => ‖z t rho‖ ^ 4) r) pDot T) :
    HasDerivAt
      (fun t => complexRadialHartreeNonlinearity (z t) r)
      0 T := by
  have hCubic := actual_complex_local_cubic_time_derivative_zero
    (fun t => z t r) T dz hU hRe hIm hZero
  have hProduct := hPotential.ofReal_comp.mul hCubic
  convert hProduct using 1
  · funext t
    unfold complexRadialHartreeNonlinearity
    ring
  · simp [hZero]

/-- The FIRST new PDE jet beyond the previously established physical
terminal velocity: real Hartree evolution forces z_tt(T,r)=0 for each
0<r<1/4. No second-jet zero hypothesis is used.

The two analytic interfaces below are (a) temporal/radial derivative
commutation for a strong classical solution and (b) differentiability
of its genuine nonlocal Hartree potential. The full original equation
is imposed locally near T, and its exact terminal value is retained. -/
theorem actual_one_orbit_terminal_Hartree_core_second_time_jet_zero
    (z zt : ℝ → ℝ → ℂ) (T r : ℝ) (pDot : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDEat : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho))
    (hr : 0 < r) (hrCore : r < 1 / 4)
    (hPDEnear : ∀ᶠ t in 𝓝 T,
      zt t r = Complex.I *
        (complexRadialLaplacian (z t) r +
          complexRadialHartreeNonlinearity (z t) r))
    (hU : HasDerivAt (fun t => z t r) (zt T r) T)
    (hRe : HasDerivAt (fun t => (z t r).re) (zt T r).re T)
    (hIm : HasDerivAt (fun t => (z t r).im) (zt T r).im T)
    (hLapCommute : HasDerivAt
      (fun t => complexRadialLaplacian (z t) r)
      (complexRadialLaplacian (zt T) r) T)
    (hPotential : HasDerivAt
      (fun t => radialHartreePotential
        (fun rho => ‖z t rho‖ ^ 4) r) pDot T) :
    HasDerivAt (fun t => zt t r) 0 T := by
  have hZero : z T r = 0 := by
    rw [hTerminal]
    have hz := actual_one_orbit_terminal_bump_zero_core
      (r := r) hrCore.le
    simp [actualOneOrbitTerminalRadiation, hz]
  have hD1 (x : ℝ) (hx0 : 0 < x) (hxCore : x < 1 / 4) :
      deriv (zt T) x = 0 := by
    have he : (zt T) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Ioo_mem_nhds hx0 hxCore] with y hy
      exact actual_one_orbit_terminal_Hartree_core_velocity_zero
        z zt T hTerminal hPDEat hy.1 hy.2
    rw [he.deriv_eq]
    exact deriv_const x 0
  have hD2 : deriv (deriv (zt T)) r = 0 := by
    have he : deriv (zt T) =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Ioo_mem_nhds hr hrCore] with x hx
      exact hD1 x hx.1 hx.2
    rw [he.deriv_eq]
    exact deriv_const r 0
  have hLapZero : complexRadialLaplacian (zt T) r = 0 := by
    simp [complexRadialLaplacian, hD1 r hr hrCore, hD2]
  have hLapTime : HasDerivAt
      (fun t => complexRadialLaplacian (z t) r) 0 T := by
    simpa only [hLapZero] using hLapCommute
  have hNLTime :=
    actual_Hartree_nonlocal_time_derivative_zero_at_core
      z T r (zt T r) pDot hU hRe hIm hZero hPotential
  have hRHS : HasDerivAt
      (fun t => Complex.I *
        (complexRadialLaplacian (z t) r +
          complexRadialHartreeNonlinearity (z t) r)) 0 T := by
    simpa using (hLapTime.add hNLTime).const_mul Complex.I
  have heq :
      (fun t => Complex.I *
        (complexRadialLaplacian (z t) r +
          complexRadialHartreeNonlinearity (z t) r)) =ᶠ[𝓝 T]
        (fun t => zt t r) := by
    filter_upwards [hPDEnear] with t ht
    exact ht.symm
  exact hRHS.congr_of_eventuallyEq heq

end HBL.TypeIIDynamicSelection
