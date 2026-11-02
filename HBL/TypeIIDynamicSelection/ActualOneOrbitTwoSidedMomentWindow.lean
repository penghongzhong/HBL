import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalRadiation
import Mathlib.Tactic

/-!
# True Hartree regular-radiation moment: uniform two-sided terminal control

The explicit nonzero smooth terminal radiation has a strictly positive
three-dimensional inverse-square quartic Hartree moment. The ACTUAL
Hartree PDE and dominated time differentiation of that same radiation
imply that its moment is continuous at the terminal physical time.

We derive BOTH upper and lower bounds on one common physical-time
neighborhood. This supplies the genuine upper moment bound needed
for the radius R=4/(kappa_H*ell*m) to contain any fixed Kummer annulus.
Previously accepted one-orbit terminal bounds only supplied the lower
moment and hence an UPPER cutoff radius. This supplies the missing
LOWER cutoff radius premise.

The full high-regularity PDE and dominated-differentiation inputs are
visible, not assumed conclusions. Nothing here proves 2.12 or
prescribes a Type-II blowup rate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Along one genuine high-regularity 3D Hartree trajectory,
the terminal positive quartic moment controls the moment from
both sides, not just below, with no invented global moment bound. -/
theorem actual_one_orbit_Hartree_terminal_two_sided_moment_window
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (I : Set ℝ) (hI : I ∈ 𝓝 T)
    (hZmeas : ∀ᶠ t in 𝓝 T,
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (fun rho => ‖z T rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho => actualRadialQuarticMomentVelocity (z T rho) (zt T rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi (0 : ℝ)))
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
    ∃ eps : ℝ, 0 < eps ∧
      ∀ t : ℝ, |t - T| < eps →
        actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation / 2 <
          actualPhysicalInverseSquareMoment (z t) ∧
        actualPhysicalInverseSquareMoment (z t) <
          2 * actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation := by
  have hmT : 0 < actualPhysicalInverseSquareMoment (z T) := by
    rw [hTerminal]
    exact actual_one_orbit_terminal_radiation_positive_moment
  have hDerivative : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t))
      (actualMomentLaplacianFlux (z T)) T :=
    actual_physical_threeD_Hartree_radiation_moment_PDE_flux
      z zt T I hI hZmeas hZint hVelMeas B hB hBound hRe hIm hPDE
  have hContinuous : ContinuousAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) T :=
    hDerivative.continuousAt
  have hLower : actualPhysicalInverseSquareMoment (z T) / 2 <
      actualPhysicalInverseSquareMoment (z T) := by linarith
  have hUpper : actualPhysicalInverseSquareMoment (z T) <
      2 * actualPhysicalInverseSquareMoment (z T) := by linarith
  have hLowerEvent : ∀ᶠ t in 𝓝 T,
      actualPhysicalInverseSquareMoment (z T) / 2 <
        actualPhysicalInverseSquareMoment (z t) :=
    hContinuous.eventually (Ioi_mem_nhds hLower)
  have hUpperEvent : ∀ᶠ t in 𝓝 T,
      actualPhysicalInverseSquareMoment (z t) <
        2 * actualPhysicalInverseSquareMoment (z T) :=
    hContinuous.eventually (Iio_mem_nhds hUpper)
  obtain ⟨eps,heps,hball⟩ :=
    Metric.mem_nhds_iff.mp (hLowerEvent.and hUpperEvent)
  refine ⟨eps,heps,?_⟩
  intro t ht
  have htBall : t ∈ Metric.ball T eps := by
    change dist t T < eps
    simpa only [Real.dist_eq] using ht
  have hBounds := hball htBall
  change
    actualPhysicalInverseSquareMoment (z T) / 2 <
      actualPhysicalInverseSquareMoment (z t) ∧
    actualPhysicalInverseSquareMoment (z t) <
      2 * actualPhysicalInverseSquareMoment (z T) at hBounds
  simpa only [hTerminal] using hBounds

end HBL.TypeIIDynamicSelection
