import HBL.TypeIIDynamicSelection.ActualOneOrbitTwoSidedMomentWindow
import HBL.TypeIIDynamicSelection.ActualHartreeWeightedPositiveOrder
import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import Mathlib.Tactic

/-!
# One genuine offterminal Hartree orbit: the full nonlocal cutoff in weighted Fredholm L²

The same physical radial inverse-square Hartree trajectory z(t) obeys the
actual PDE throughout its local high-regularity existence interval.
The positive terminal quartic moment, together with its PDE-derived
time continuity, provides a uniform strictly positive m0 on a
two-sided physical-time neighborhood of T.

Strauss radial H¹ decay and a uniform L-infinity bound of that SAME
trajectory supply the exact quartic Riesz envelope. This file combines
previously audited estimates for the genuine nonlocal inverse-square
Hartree commutator and physical moment-selected moving cutoff
R(t,ell)=4/(kappa_H*ell*m[z(t)]).

For every 3/2 < sigma < 2 and every 0 < ell <= 1, uniformly in that
time neighborhood, the ORIGINAL weighted Fredholm L² norm of the
complete nonlocal cutoff commutator is bounded by C*ell^(2-sigma).
Neither a separate decay/rate hypothesis, nor an abstract generated
source order, nor a local cubic substitute for the Riesz potential
is used.

This is a genuine OFFTERMINAL component of revised 2.13.
It does NOT yet control the *mixed* linear V³Z source, finish Kummer
C¹ inner/outer matching, or prove the full generated-source recursion.
It does NOT certify original environment 2.13 or 12/13.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Uniform positive weighted-L² gain for the full inverse-square
Hartree nonlocal moving cutoff commutator along ONE actual PDE
trajectory, with the cutoff radius selected by its actual quartic
moment. No Type-II rate is an input. -/
theorem actual_one_Hartree_orbit_offterminal_full_nonlocal_weighted_Riesz_gain
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
    (majorant : ℝ → ℝ) (hInt : IntegrableOn majorant (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤
        majorant rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (zt t rho).im t)
    (hPDEall : ∀ t ∈ I, ∀ rho : ℝ, 0 < rho →
      zt t rho = Complex.I *
        (complexRadialLaplacian (z t) rho +
          complexRadialHartreeNonlinearity (z t) rho))
    (B A sigma : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSigmaLo : 3 / 2 < sigma) (hSigmaHi : sigma < 2)
    (hz : ∀ t ∈ I, Measurable (z t))
    (hSup : ∀ t ∈ I, ∀ u : ℝ, 0 < u → ‖z t u‖ ≤ B)
    (hStrauss : ∀ t ∈ I, ∀ u : ℝ, 1 ≤ u → u * ‖z t u‖ ≤ A) :
    ∃ delta m0 : ℝ, 0 < delta ∧ 0 < m0 ∧
      ∀ t : ℝ, |t - T| < delta → t ∈ I →
        ∀ ell : ℝ, 0 < ell → ell ≤ 1 →
          (eLpNorm
            (fun r : ℝ => affineJapaneseWeight sigma r *
              ‖actualHartreeNonlocalCutoffError
                (actualHartreeMomentCutoffRadius ell
                  (radialPhysicalQuarticMoment (z t))) ell (z t) r‖)
            2 halfLineMeasure).toReal ≤
          ((2 * radialHartreeRowBoundConstant *
                (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
            ((1 + (2 * (4 / (hartreeKappa * m0))) ^ 2) ^ (sigma / 2) *
              Real.sqrt (2 * (4 / (hartreeKappa * m0))))) *
            ell ^ (2 - sigma) := by
  have hTmem : T ∈ I := mem_of_mem_nhds hI
  have hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho) :=
    hPDEall T hTmem
  obtain ⟨delta,hDelta,hWindow⟩ :=
    actual_one_orbit_Hartree_terminal_two_sided_moment_window
      z zt T hTerminal I hI hZmeas hZint hVelMeas
      majorant hInt hBound hRe hIm hPDE
  have hmT : 0 < radialPhysicalQuarticMoment
      actualOneOrbitTerminalRadiation := by
    have hp := actual_one_orbit_terminal_radiation_positive_moment
    simpa only [actual_physical_inverse_square_radial_reduction] using hp
  let m0 : ℝ :=
    radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation / 2
  have hm0 : 0 < m0 := by
    dsimp [m0]
    linarith
  have hD : 0 ≤ 2 * (B ^ 4 + A ^ 4) := by positivity
  refine ⟨delta,m0,hDelta,hm0,?_⟩
  intro t ht htI ell hell hellOne
  have hm0m : m0 ≤ radialPhysicalQuarticMoment (z t) := by
    have hlow := (hWindow t ht).1
    dsimp [m0]
    simpa only [actual_physical_inverse_square_radial_reduction] using hlow.le
  exact actual_Hartree_physical_nonlocal_Riesz_positive_Fredholm_gain
    ell (radialPhysicalQuarticMoment (z t)) m0
    B (2 * (B ^ 4 + A ^ 4)) sigma
    hell hellOne hm0 hm0m hB hD hSigmaLo hSigmaHi
    (z t) (hz t htI) (hSup t htI)
    (actual_Hartree_radial_quartic_envelope_from_Strauss
      (z t) B A hB hA (hSup t htI) (hStrauss t htI))

end HBL.TypeIIDynamicSelection
