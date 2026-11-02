import HBL.TypeIIDynamicSelection.ActualHartreeOffterminalMixedQuadraticGain
import HBL.TypeIIDynamicSelection.ActualOneOrbitTwoSidedMomentWindow
import Mathlib.Tactic

/-!
# Revised 2.13: one genuine Hartree orbit, uniform offterminal mixed quartic source

This is a genuine *offterminal* estimate, not an evaluation only on the
artificially compact terminal datum. We use the same actual 3D radial
inverse-square Hartree physical trajectory z(t,r) at every t near T.
The terminal moment of that orbit is positive by the actual selected
nonzero regular radiation; the true Hartree PDE with dominated
differentiation makes its quartic moment continuous near T.

The genuine moment-selected monopole strength
   c(t,ell)=kappa_H*ell*m[z(t)]
has |c|<=1 when ell is below an EXPLICIT threshold derived
from the terminal moment. The actual moving monopole Fredholm
profile then has a uniform bound on all positive radii.
The exact mixed quartic polynomial and critical radiation scaling
Z_ell(t,r)=sqrt(ell)*z(t,ell*r) give the uniform quadratic/cubic
source gain O(ell), simultaneously for all those t and r.

High-regularity radial L-infinity amplitude bounds are the usual
visible physical local-theory interface. There is NO assumed
concentration/blowup exponent or manufactured GeneratedTerm.order.

Still OPEN: the linear mixed source, weighted global L2 Riesz
estimates, actual parameter derivatives, outer Kummer/remote
interface matching and the whole original nonlinear finite profile.
This theorem is a proper auxiliary to revised 2.13, not 12/13.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Uniform in genuine physical time, radius, and sufficiently small
critical length: the physical quartic Hartree mixed density's
quadratic-and-cubic remainder has a TRUE positive ell power. -/
theorem actual_one_Hartree_orbit_offterminal_mixed_higher_uniform_gain
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
    (B : ℝ) (hB : 0 ≤ B)
    (hSup : ∀ t ∈ I, ∀ u : ℝ, 0 < u → ‖z t u‖ ≤ B) :
    ∃ delta ellMax : ℝ, 0 < delta ∧ 0 < ellMax ∧
      ∀ t : ℝ, |t - T| < delta → t ∈ I →
        ∀ ell : ℝ, 0 < ell → ell ≤ ellMax →
          ∀ r : ℝ, 0 < r →
            |actualWholeRadiationMixedHigher
                (monopolePerturbedRadialProfile
                  (monopoleQuadraticRadius
                    (hartreeKappa * ell *
                      radialPhysicalQuarticMoment (z t)))
                  (hartreeKappa * ell *
                    radialPhysicalQuarticMoment (z t)))
                (rescalePhysicalRadiation ell (z t)) r| ≤
              (6 * (1 + monopoleRadialBoundConstant) ^ 2 * B ^ 2 +
                4 * (1 + monopoleRadialBoundConstant) * B ^ 3) * ell := by
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
  let mT : ℝ :=
    radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation
  have hmT : 0 < mT := by
    have hp := actual_one_orbit_terminal_radiation_positive_moment
    simpa only [mT, actual_physical_inverse_square_radial_reduction]
      using hp
  let M : ℝ := 2 * mT
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  let ellMax : ℝ := min 1 (1 / (hartreeKappa * M))
  have hEllMax : 0 < ellMax := by
    dsimp [ellMax]
    exact lt_min (by norm_num) (div_pos (by norm_num) (mul_pos hk hM))
  refine ⟨delta,ellMax,hDelta,hEllMax,?_⟩
  intro t ht htI ell hell hellMax r hr
  obtain ⟨hlo,hhi⟩ := hWindow t ht
  have hmLe :
      radialPhysicalQuarticMoment (z t) ≤ M := by
    have hu : actualPhysicalInverseSquareMoment (z t) <
        2 * actualPhysicalInverseSquareMoment
          actualOneOrbitTerminalRadiation := hhi
    simpa only [M, mT, actual_physical_inverse_square_radial_reduction]
      using hu.le
  have hEllOne : ell ≤ 1 :=
    hellMax.trans (min_le_left _ _)
  have hEllM : ell ≤ 1 / (hartreeKappa * M) :=
    hellMax.trans (min_le_right _ _)
  have hCM : hartreeKappa * M * ell ≤ 1 := by
    calc
      hartreeKappa * M * ell = ell * (hartreeKappa * M) := by ring
      _ ≤ 1 := (le_div_iff₀ (mul_pos hk hM)).mp hEllM
  have hCprod :
      hartreeKappa * ell * radialPhysicalQuarticMoment (z t) ≤
        1 := by
    have hMul :
        (hartreeKappa * ell) * radialPhysicalQuarticMoment (z t) ≤
          (hartreeKappa * ell) * M :=
      mul_le_mul_of_nonneg_left hmLe (by positivity)
    calc
      hartreeKappa * ell * radialPhysicalQuarticMoment (z t) ≤
          hartreeKappa * ell * M := hMul
      _ = hartreeKappa * M * ell := by ring
      _ ≤ 1 := hCM
  have hm0 : 0 ≤ radialPhysicalQuarticMoment (z t) := by
    have hpos : 0 < actualPhysicalInverseSquareMoment (z t) := by
      have hterm : 0 < actualPhysicalInverseSquareMoment
          actualOneOrbitTerminalRadiation :=
        actual_one_orbit_terminal_radiation_positive_moment
      linarith
    simpa only [actual_physical_inverse_square_radial_reduction] using hpos.le
  have hCoef :
      |hartreeKappa * ell * radialPhysicalQuarticMoment (z t)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact hCprod
  have hzAt : ‖z t (ell * r)‖ ≤ B :=
    hSup t htI (ell * r) (mul_pos hell hr)
  exact actual_Hartree_offterminal_moment_monopole_mixed_higher_length_gain
    t ell (radialPhysicalQuarticMoment (z t)) B r
    hell hEllOne hr hB hCoef z hzAt

end HBL.TypeIIDynamicSelection
