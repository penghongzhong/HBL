import HBL.RadialHartreePotential
import HBL.MonopoleHartreeDensity

/-! Absolute convergence of the actual truncated monopole's nonlinear Riesz potential. -/

noncomputable section
open Set MeasureTheory

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The Riesz potential of the actual fourth-power density remainder. -/
def monopoleHartreePotential (R c r : ℝ) : ℝ :=
  radialHartreePotential (monopoleHartreeDensityRemainder R c) r

/-- The actual nonlinear density has an absolutely convergent radial potential.
Only the cutoff radius, amplitude range and positive evaluation radius are assumed. -/
theorem monopoleHartreePotential_integrable {R c r : ℝ}
    (hR : 0 < R) (hc : |c| ≤ 1) (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopoleHartreeDensityRemainder R c rho) (Ioi (0 : ℝ)) := by
  let F := (Ioi (0 : ℝ)).indicator (monopoleHartreeDensityRemainder R c)
  have hf : Measurable F :=
    (monopoleHartreeDensityRemainder_measurable R c).indicator measurableSet_Ioi
  have hcomp : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc 0 (2 * R)))
    apply Function.support_subset_iff'.mpr
    intro rho hnot
    by_cases hp : rho ∈ Ioi (0 : ℝ)
    · have hlarge : 2 * R < rho := by
        apply lt_of_not_ge
        intro hh
        exact hnot ⟨hp.le, hh⟩
      simp only [F, indicator_of_mem hp]
      exact monopoleHartreeDensityRemainder_zero_of_two_mul_le hR hlarge.le
    · exact indicator_of_notMem hp _
  have hM : 0 ≤ monopoleHartreeDensityBoundConstant * c ^ 2 := by
    have hB := monopoleRadialBoundConstant_pos
    unfold monopoleHartreeDensityBoundConstant
    positivity
  have hb : ∀ rho : ℝ, |F rho| ≤ monopoleHartreeDensityBoundConstant * c ^ 2 := by
    intro rho
    by_cases hp : rho ∈ Ioi (0 : ℝ)
    · simpa only [F, indicator_of_mem hp] using
        (monopoleHartreeDensityRemainder_abs_le (R := R) hp hc)
    · simpa only [F, indicator_of_notMem hp, abs_zero] using hM
  have hi := radialHartreePotential_integrable F hf hcomp hb hr
  refine hi.congr_fun ?_ measurableSet_Ioi
  intro rho hrho
  simp only [F, indicator_of_mem hrho]

end HBL.Modulation.Monopole
