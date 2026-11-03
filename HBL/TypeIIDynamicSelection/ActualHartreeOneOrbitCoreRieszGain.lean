import HBL.TypeIIDynamicSelection.ActualHartreeMomentSelectedCoreRieszGain
import HBL.TypeIIDynamicSelection.ActualOneOrbitTwoSidedMomentWindow
import Mathlib.Tactic

/-!
# Strict HBL 2.13 supporting lemma: one true Hartree PDE trajectory has
# O(ell) moving-monopole core Riesz source in a physical terminal window

The SAME actual 3D inverse-square Hartree radial physical trajectory
z(t,r) supplies its positive quartic moment m(t). The physical PDE
and dominated moment differentiation yield a genuine two-sided
terminal-time window, from which the moving-monopole center amplitude
c(t,ell)=kappa_H*ell*m(t) automatically obeys |c|<=1 for all
0<ell<=ellMax.

The already certified exact Riesz expansion proves
  |I[V_c^4](r)-3*W(r)^2| <= C*ell
uniformly in t and r>0 on that window. No prescribed Type-II
blowup exponent or independent radiation-source smallness appears.

These are explicit high-regularity physical local-flow / dominated
moment interfaces, not added Lean axioms. The full revised finite
profile and dynamical blowup existence theorem remain OPEN.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The real physical Hartree PDE itself selects the moving monopole
amplitude and makes its complete nonlocal quartic core potential
O(ell) near the physical terminal time, for every positive radius. -/
theorem actual_one_Hartree_orbit_offterminal_core_Riesz_length_gain
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
          complexRadialHartreeNonlinearity (z t) rho)) :
    ∃ delta ellMax C : ℝ, 0 < delta ∧ 0 < ellMax ∧
      0 ≤ C ∧
      ∀ t : ℝ, |t - T| < delta → t ∈ I →
        ∀ ell : ℝ, 0 < ell → ell ≤ ellMax →
          ∀ r : ℝ, 0 < r →
            |radialHartreePotential
                (fun rho => monopolePerturbedRadialProfile
                  (monopoleQuadraticRadius
                    (hartreeKappa * ell *
                      radialPhysicalQuarticMoment (z t)))
                  (hartreeKappa * ell *
                    radialPhysicalQuarticMoment (z t)) rho ^ 4) r -
              3 * bubble r ^ 2| ≤ C * ell := by
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
  let K : ℝ := hartreeKappa * M
  have hK : 0 < K := mul_pos hk hM
  let ellMax : ℝ := min 1 (1 / K)
  have hEllMax : 0 < ellMax := by
    dsimp [ellMax]
    exact lt_min (by norm_num) (div_pos (by norm_num) hK)
  let C : ℝ :=
    4 * K * (radialHartreeRowBoundConstant *
      monopoleRadialBoundConstant) +
      monopoleHartreePotentialBoundConstant * K ^ 2
  have hC : 0 ≤ C := by
    dsimp [C,K]
    have hmon := monopoleRadialBoundConstant_pos
    have hrow := radialHartreeRowBoundConstant_pos
    have hbase := radialHartreeBubbleBoundConstant_pos
    unfold monopoleHartreePotentialBoundConstant
      monopoleHartreeDensityDecayConstant
    positivity
  refine ⟨delta,ellMax,C,hDelta,hEllMax,hC,?_⟩
  intro t ht htI ell hell hellMax r hr
  have hmLe : radialPhysicalQuarticMoment (z t) ≤ M := by
    have hu : actualPhysicalInverseSquareMoment (z t) <
        2 * actualPhysicalInverseSquareMoment
          actualOneOrbitTerminalRadiation := (hWindow t ht).2
    simpa only [M,mT, actual_physical_inverse_square_radial_reduction]
      using hu.le
  have hm0 : 0 ≤ radialPhysicalQuarticMoment (z t) := by
    have hpos : 0 < actualPhysicalInverseSquareMoment (z t) := by
      have hterm : 0 < actualPhysicalInverseSquareMoment
          actualOneOrbitTerminalRadiation :=
        actual_one_orbit_terminal_radiation_positive_moment
      linarith [(hWindow t ht).1]
    simpa only [actual_physical_inverse_square_radial_reduction]
      using hpos.le
  have hBoundEll : ell ≤ min 1 (1 / (hartreeKappa * M)) := by
    simpa only [ellMax,K] using hellMax
  have hReal := actual_Hartree_moment_selected_core_Riesz_length_gain
    ell (radialPhysicalQuarticMoment (z t)) M r
    hell hM hm0 hmLe hBoundEll hr
  simpa only [C,K] using hReal

end HBL.TypeIIDynamicSelection
