import HBL.TypeIIDynamicSelection.ActualHartreeMomentRadiusWindow
import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalRadiation
import Mathlib.Tactic

/-!
# Original HBL 2.12: actual Hartree terminal positivity fixes the whole moving radius

The same explicitly selected nonzero terminal annular radiation has
positive TRUE three-dimensional inverse-square quartic moment. From
the actual physical Hartree PDE, dominated differentiation gives a
continuous terminal moment. Its strict positive lower bound hence
yields the matching physical overlap R=4/(kappa_H*ell*m(t)) bound
R<=C_g/ell on the SAME actual solution.

This is a non-circular proof: the terminal datum and moment are actual,
and the moment PDE is an explicit real high-regularity input.
No upper Type-II blowup exponent or arbitrary prescribed moment is
assumed. The conclusion is a radius estimate, not all of original 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The nonzero explicit physical Hartree terminal datum gives
a positive uniform lower moment and an upper moving R(s) window.
The relative radius estimate is derived from the actual PDE-moment
derivative, not supplied as an independent assumption. -/
theorem actual_one_orbit_physical_Hartree_terminal_radius_upper
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (I : Set ℝ)
    (hI : I ∈ 𝓝 T)
    (hZmeas : ∀ᶠ t in 𝓝 T,
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (fun rho => ‖z T rho‖ ^ 4) (Ioi (0 : ℝ)))
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
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, |t - T| < ε → ∀ ell : ℝ, 0 < ell →
        actualHartreeMomentCutoffRadius ell
            (radialPhysicalQuarticMoment (z t)) ≤
          (4 / (hartreeKappa *
            (radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation / 2)))
            / ell := by
  obtain ⟨ε,hε,hWindow⟩ :=
    actual_one_orbit_Hartree_terminal_positive_moment_window
      z zt T hTerminal I hI hZmeas hZint hVelMeas
      B hB hBound hRe hIm hPDE
  have hStart : 0 < radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation := by
    simpa only [actual_physical_inverse_square_radial_reduction] using
      actual_one_orbit_terminal_radiation_positive_moment
  refine ⟨ε,hε,?_⟩
  intro t ht ell hell
  have hMomentLower :
      radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation / 2 ≤
        radialPhysicalQuarticMoment (z t) := by
    have h := hWindow t ht
    simpa only [actual_physical_inverse_square_radial_reduction] using h.le
  exact actual_Hartree_positive_moment_upper_cutoff_radius
    ell (radialPhysicalQuarticMoment (z t))
    (radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation / 2)
    hell (by positivity) hMomentLower

end HBL.TypeIIDynamicSelection
