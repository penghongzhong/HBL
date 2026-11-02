import HBL.TypeIIDynamicSelection.ActualHartreeStraussPositiveFredholm
import HBL.TypeIIDynamicSelection.ActualOneOrbitPhysicalTerminalRadiusWindow
import Mathlib.Tactic

/-!
# ORIGINAL 2.12: uniform genuine weighted Riesz source along ONE physical Hartree orbit

For the single real nonzero smooth annular terminal datum g selected
by the HBL existence manuscript, the ACTUAL 3D Hartree PDE and
dominated quartic-moment differentiation show the genuine whole
moment m(t) stays uniformly positive close to T.

The cited Strauss radial H1 lemma + standard high Sobolev L-infinity
bounds supply fixed constants A,B for that SAME physical orbit
on the local regular-flow interval. Combining the earlier
kernel-checked quantitative Riesz source estimate with this
PDE-derived moment window yields one uniform bound:

 || <r>^sigma [N(chi_{R(t,ell)} f_{t,ell}) -
             chi_{R(t,ell)} N(f_{t,ell})] ||_L2(0,infty)
       <= C_g(A,B,sigma) * ell^(2-sigma),  3/2<sigma<2,

R(t,ell)=4/(kappa_H*ell*m(t)), f_{t,ell}=sqrt(ell)*z(t,ell r).

The UNIFORM time bounds A,B and radial pointwise representative
are explicit legitimate high-regularity literature interfaces.
No rate law for ell(s), no externalized HBL 2.12, and no arbitrary
quartic tail assumption is introduced. This controls the PURE
radiation nonlocal cutoff part; full Vc+Z mixed / Kummer
interface / generated term hierarchy remains unproved.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.AffineTail HBL.Modulation.Monopole

/-- For ONE actual Hartree physical flow near its nonzero radial
terminal radiation, the true nonlocal cutoff error has a UNIFORM
positive exponent in the ORIGINAL weighted Fredholm space.
Neither terminal compact-support persistence nor an independent
Riesz-source order is assumed. -/
theorem actual_Hartree_one_physical_orbit_uniform_positive_weighted_Riesz
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
    (velBound : ℝ → ℝ)
    (hVelInt : IntegrableOn velBound (Ioi (0 : ℝ)))
    (hVelBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ velBound rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho))
    (B A sigma : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSigmaLo : 3 / 2 < sigma) (hSigmaHi : sigma < 2)
    (hzMeas : ∀ t ∈ I, Measurable (z t))
    (hSup : ∀ t ∈ I, ∀ u : ℝ, 0 < u → ‖z t u‖ ≤ B)
    (hStrauss : ∀ t ∈ I, ∀ u : ℝ, 1 ≤ u → u * ‖z t u‖ ≤ A) :
    ∃ eps C : ℝ, 0 < eps ∧ 0 ≤ C ∧
      ∀ t : ℝ, |t - T| < eps → t ∈ I →
        ∀ ell : ℝ, 0 < ell → ell ≤ 1 →
          (eLpNorm
            (fun r : ℝ => affineJapaneseWeight sigma r *
              ‖actualHartreeNonlocalCutoffError
                (actualHartreeMomentCutoffRadius ell
                  (radialPhysicalQuarticMoment (z t)))
                ell (z t) r‖)
            2 halfLineMeasure).toReal ≤ C * ell ^ (2 - sigma) := by
  obtain ⟨eps,heps,hWindow⟩ :=
    actual_one_orbit_Hartree_terminal_positive_moment_window
      z zt T hTerminal I hI hZmeas hZint hVelMeas
      velBound hVelInt hVelBound hRe hIm hPDE
  let m0 : ℝ :=
    radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation / 2
  have hm0 : 0 < m0 := by
    have hPos : 0 < radialPhysicalQuarticMoment
        actualOneOrbitTerminalRadiation := by
      simpa only [actual_physical_inverse_square_radial_reduction] using
        actual_one_orbit_terminal_radiation_positive_moment
    dsimp [m0]
    exact half_pos hPos
  let Q : ℝ := 4 / (hartreeKappa * m0)
  let C : ℝ :=
    (2 * radialHartreeRowBoundConstant *
      (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
        ((1 + (2 * Q) ^ 2) ^ (sigma / 2) *
          Real.sqrt (2 * Q))
  have hC : 0 ≤ C := by
    dsimp [C,Q]
    have hk : 0 < hartreeKappa := by
      unfold hartreeKappa
      positivity
    have hrow := radialHartreeRowBoundConstant_pos
    positivity
  refine ⟨eps,C,heps,hC,?_⟩
  intro t ht htI ell hell hellOne
  have hMomentLower : m0 ≤ radialPhysicalQuarticMoment (z t) := by
    have h := (hWindow t ht).le
    simpa only [m0, actual_physical_inverse_square_radial_reduction]
      using h
  have hBound :=
    actual_Hartree_radial_Strauss_true_Fredholm_positive_gain
      ell (radialPhysicalQuarticMoment (z t))
      m0 B A sigma hell hellOne hm0 hMomentLower
      hB hA hSigmaLo hSigmaHi (z t) (hzMeas t htI)
      (hSup t htI) (hStrauss t htI)
  simpa only [C,Q] using hBound

end HBL.TypeIIDynamicSelection
