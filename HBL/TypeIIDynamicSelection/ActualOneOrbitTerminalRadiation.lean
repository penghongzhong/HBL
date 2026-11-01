import HBL.TypeIIDynamicSelection.ActualCutoffUniformTransport
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
# Explicit nonzero smooth terminal radial radiation for ONE Hartree Type II orbit

This source constructs a real smooth radial annular profile g(r) by using
ONLY the original paper's actual smooth cutoff, then shows that:
- g vanishes throughout the inner radius r <= 1/4;
- g equals one throughout 1/2 <= r <= 2;
- g vanishes for r >= 4;
- its genuine three-dimensional inverse-square quartic moment
    m0[g] = 4*pi * integral_(0,+infty) |g(r)|^4 dr
  is strictly positive and finite.

Thus the previously proved nonzero terminal moment condition is
consistent with an explicit flat-at-origin radiation choice. The
separate Sobolev H^L radial-lift statement, actual regular Hartree
flow for this g, uniform moment derivative on its terminal interval,
and the true Type II PDE orbit remain future obligations. This
does NOT count as a newly closed complete original environment.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail HBL.Modulation.Monopole

/-- Explicit bounded smooth annular radial terminal source, with no
near-origin radiation. -/
def actualOneOrbitTerminalBump (r : ℝ) : ℝ :=
  cutoff (4 * r) * (1 - cutoff (r / 2))

def actualOneOrbitTerminalRadiation (r : ℝ) : ℂ :=
  (actualOneOrbitTerminalBump r : ℂ)

theorem actual_one_orbit_terminal_bump_smooth :
    ContDiff ℝ ∞ actualOneOrbitTerminalBump := by
  have hfirst : ContDiff ℝ ∞ (fun r : ℝ => cutoff (4 * r)) :=
    cutoff_contDiff_infty.comp (contDiff_const.mul contDiff_id)
  have hsecond : ContDiff ℝ ∞ (fun r : ℝ => cutoff (r / 2)) :=
    cutoff_contDiff_infty.comp (contDiff_id.div_const 2)
  exact hfirst.mul (contDiff_const.sub hsecond)

theorem actual_one_orbit_terminal_bump_zero_core
    {r : ℝ} (hr : r ≤ 1 / 4) :
    actualOneOrbitTerminalBump r = 0 := by
  have hc : cutoff (4 * r) = 0 :=
    cutoff_zero_of_le_one (4 * r) (by linarith)
  simp [actualOneOrbitTerminalBump, hc]

theorem actual_one_orbit_terminal_bump_one_annulus
    {r : ℝ} (hlo : 1 / 2 ≤ r) (hhi : r ≤ 2) :
    actualOneOrbitTerminalBump r = 1 := by
  have hc1 : cutoff (4 * r) = 1 :=
    cutoff_one_of_two_le (4 * r) (by linarith)
  have hc2 : cutoff (r / 2) = 0 :=
    cutoff_zero_of_le_one (r / 2) (by linarith)
  simp [actualOneOrbitTerminalBump, hc1, hc2]

theorem actual_one_orbit_terminal_bump_zero_far
    {r : ℝ} (hr : 4 ≤ r) :
    actualOneOrbitTerminalBump r = 0 := by
  have hc : cutoff (r / 2) = 1 :=
    cutoff_one_of_two_le (r / 2) (by linarith)
  simp [actualOneOrbitTerminalBump, hc]

/-- The actual 3D Hartree radiation moment of an explicitly selected
nonzero smooth annular datum is STRICTLY positive. This proves the
one-orbit nondegeneracy condition at terminal time without assuming
the conclusion or postulating a mass. -/
theorem actual_one_orbit_terminal_radiation_positive_moment :
    0 < actualPhysicalInverseSquareMoment
      actualOneOrbitTerminalRadiation := by
  let F : ℝ → ℝ := fun r => ‖actualOneOrbitTerminalRadiation r‖ ^ 4
  have hGcont : Continuous actualOneOrbitTerminalBump :=
    actual_one_orbit_terminal_bump_smooth.continuous
  have hZcont : Continuous actualOneOrbitTerminalRadiation :=
    Complex.continuous_ofReal.comp hGcont
  have hFcont : Continuous F := hZcont.norm.pow 4
  have hFsupport : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (1 / 4 : ℝ) 4))
    intro r hr
    by_contra hn
    have hout : r < (1 / 4 : ℝ) ∨ 4 < r := by
      by_cases hl : r < (1 / 4 : ℝ)
      · exact Or.inl hl
      · have hnot4 : ¬ r ≤ 4 := by
          intro h4
          exact hn ⟨le_of_not_gt hl, h4⟩
        exact Or.inr (lt_of_not_ge hnot4)
    have hfzero : F r = 0 := by
      rcases hout with hl | hh
      · have he := actual_one_orbit_terminal_bump_zero_core
          (r := r) (le_of_lt hl)
        simp [F, actualOneOrbitTerminalRadiation, he]
      · have he := actual_one_orbit_terminal_bump_zero_far
          (r := r) (le_of_lt hh)
        simp [F, actualOneOrbitTerminalRadiation, he]
    exact hr hfzero
  have hFint : IntegrableOn F (Ioi (0 : ℝ)) :=
    (hFcont.integrable_of_hasCompactSupport hFsupport).integrableOn
  have hFnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi (0 : ℝ))] F :=
    Filter.Eventually.of_forall (fun r => pow_nonneg (norm_nonneg _) 4)
  have hsupp : Ioo (1 / 2 : ℝ) 2 ⊆
      Function.support F ∩ Ioi (0 : ℝ) := by
    intro r hr
    have hg : actualOneOrbitTerminalBump r = 1 :=
      actual_one_orbit_terminal_bump_one_annulus hr.1.le hr.2.le
    constructor
    · change F r ≠ 0
      simp [F, actualOneOrbitTerminalRadiation, hg]
    · exact (show (0 : ℝ) < 1 / 2 by norm_num).trans hr.1
  have hinterval : 0 < (volume : Measure ℝ) (Ioo (1 / 2 : ℝ) 2) :=
    isOpen_Ioo.measure_pos _ ⟨1, by norm_num⟩
  have hsupportpos :
      0 < (volume : Measure ℝ) (Function.support F ∩ Ioi (0 : ℝ)) :=
    hinterval.trans_le (measure_mono hsupp)
  have hintpos : 0 < ∫ r in Ioi (0 : ℝ), F r :=
    (setIntegral_pos_iff_support_of_nonneg_ae hFnonneg hFint).2 hsupportpos
  rw [actual_physical_inverse_square_radial_reduction]
  change 0 < 4 * Real.pi * ∫ r in Ioi (0 : ℝ), F r
  exact mul_pos (by positivity) hintpos



/-- For the EXPLICIT smooth, flat-at-origin nonzero annular terminal
radiation constructed above, continuity of the physical Hartree quartic
moment on the genuine terminal solution is DERIVED from the original
PDE plus Mathlib's dominated differentiation theorem.

Consequently the genuine physical 3D inverse-square moment stays
bounded away from zero on a terminal time neighborhood. There is no
assumption HasDerivAt(m0), no prescribed blowup rate, and no
assumption of a uniform positive moment for every small datum.
The remaining high-regularity PDE/dominated source hypotheses are
spelled out explicitly and must be instantiated by the local theory. -/
theorem actual_one_orbit_Hartree_terminal_positive_moment_window
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
    (hBound : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t - T| < ε →
      actualPhysicalInverseSquareMoment
        actualOneOrbitTerminalRadiation / 2 <
        actualPhysicalInverseSquareMoment (z t) := by
  have hpos : 0 < actualPhysicalInverseSquareMoment (z T) := by
    rw [hTerminal]
    exact actual_one_orbit_terminal_radiation_positive_moment
  have hderiv : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t))
      (actualMomentLaplacianFlux (z T)) T :=
    actual_physical_threeD_Hartree_radiation_moment_PDE_flux
      z zt T I hI hZmeas hZint hVelMeas B hB hBound hRe hIm hPDE
  have hcontinuous : ContinuousAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) T :=
    hderiv.continuousAt
  have hhalf :
      actualPhysicalInverseSquareMoment (z T) / 2 <
        actualPhysicalInverseSquareMoment (z T) := by
    linarith
  have hev : ∀ᶠ t in 𝓝 T,
      actualPhysicalInverseSquareMoment (z T) / 2 <
        actualPhysicalInverseSquareMoment (z t) :=
    hcontinuous.eventually (Ioi_mem_nhds hhalf)
  obtain ⟨ε, hε, hsubset⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have hball : t ∈ Metric.ball T ε := by
    change dist t T < ε
    simpa only [Real.dist_eq] using ht
  have hpositive := hsubset hball
  change actualPhysicalInverseSquareMoment (z T) / 2 <
    actualPhysicalInverseSquareMoment (z t) at hpositive
  simpa only [hTerminal] using hpositive

end HBL.TypeIIDynamicSelection
