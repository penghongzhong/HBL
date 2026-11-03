import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInnerFredholm
import HBL.TypeIIDynamicSelection.ActualHartreeEighthEnvelopeL2Integral
import Mathlib.Tactic

/-!
# HBL revised 2.13: the SAME radial source has a complementary exterior L2 space

The original PDE's half-line source is r*F where F is the FULL actual
quartic inverse-square Hartree interaction, not a truncated Riesz density.
The inner correction uses r*(1-cutoff(r/R))*F in the stronger
Fredholm L^(2,7/4) space.  The exterior complement r*cutoff(r/R)*F
belongs to the weaker L²(dr) space.  This is mathematically natural:
multiplication by r loses one radial weight, which need not be paid
twice in the exterior equation.

The exact inner+exterior partition remains valid for ONE physical F.
All bounds below are derived from the accepted actual 10-term source
estimate, not assumed on either regional source.  Theorems below do
not assert remote Green solvability, matching, time order or blowup.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- The exterior complement to the actual conjugated inner interaction.
The cutoff is applied AFTER the original global nonlocal convolution. -/
def actualHartreeRadiallyConjugatedExteriorSource
    (R ell c : ℝ) (z : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((r * cutoff (r / R) : ℝ) : ℂ) *
    actualHartreePhysicalSliceInteraction ell c z r

/-- Original q=r*u forcing split: nothing nonlinear is dropped or
commuted through a Hartree Riesz potential. -/
theorem actual_Hartree_one_source_exact_inner_exterior_partition
    (R ell c r : ℝ) (z : ℝ → ℂ) :
    (r : ℂ) * actualHartreePhysicalSliceInteraction ell c z r =
      actualHartreeRadiallyConjugatedInnerSource R ell c z r +
      actualHartreeRadiallyConjugatedExteriorSource R ell c z r := by
  simpa only [actualHartreeRadiallyConjugatedExteriorSource] using
    actual_Hartree_conjugated_interaction_exact_partition R ell c r z

/-- The actual exterior interaction vanishes on the physical inner
region of the same smooth partition. -/
theorem actual_Hartree_exterior_source_zero_before_inner_radius
    (R ell c r : ℝ) (z : ℝ → ℂ)
    (hR : 0 < R) (hr : r ≤ R) :
    actualHartreeRadiallyConjugatedExteriorSource R ell c z r = 0 := by
  have hSmall : r / R ≤ 1 :=
    (div_le_iff₀ hR).2 (by simpa using hr)
  unfold actualHartreeRadiallyConjugatedExteriorSource
  rw [cutoff_zero_of_le_one (r / R) hSmall]
  simp

/-- Exterior r*F is automatically in the correct unweighted L² half-line
space; its squared norm has an explicit O(ell^(1/4)) physical bound.
The inner region has stronger L^(2,7/4) membership separately.
No exterior source membership or artificial generated order is assumed. -/
theorem actual_Hartree_conjugated_exterior_unweighted_L2
    (R ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let G : ℝ → ℂ :=
      actualHartreeRadiallyConjugatedExteriorSource R ell c z
    MemLp (fun r : ℝ => ‖G r‖) 2 halfLineMeasure ∧
      (∫ r in Ioi (0 : ℝ), ‖G r‖ ^ 2) ≤
        (actualHartreePhysicalWeightedSourceConstant B A *
          ell ^ (1 / 8 : ℝ)) ^ 2 *
          (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ))) := by
  let F : ℝ → ℂ := actualHartreePhysicalSliceInteraction ell c z
  let G : ℝ → ℂ := actualHartreeRadiallyConjugatedExteriorSource R ell c z
  let K : ℝ := actualHartreePhysicalWeightedSourceConstant B A
  have hK : 0 ≤ K :=
    actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
  have hF : Measurable F :=
    actual_Hartree_physical_slice_source_measurable ell c z hz
  have hCut : Measurable (fun r : ℝ => cutoff (r / R)) :=
    cutoff_contDiff_infty.continuous.measurable.comp
      (measurable_id.div_const R)
  have hG : Measurable G := by
    dsimp only [G, actualHartreeRadiallyConjugatedExteriorSource]
    exact (Complex.measurable_ofReal.comp (measurable_id.mul hCut)).mul hF
  have hCutRange (r : ℝ) : 0 ≤ cutoff (r / R) ∧
      cutoff (r / R) ≤ 1 := by
    obtain ⟨h0,h1⟩ := actual_Hartree_inner_source_cutoff_range R r
    dsimp [actualHartreeInnerSourceCutoff] at h0 h1
    constructor <;> linarith
  have hPoint (r : ℝ) (hr : 0 < r) :
      ‖G r‖ ≤ K * ell ^ (1 / 8 : ℝ) *
        (1 + r) ^ (-(5 / 8 : ℝ)) := by
    let d : ℝ := 1 + r
    have hd : 0 < d := by dsimp [d]; linarith
    have hdOne : 1 ≤ d := by dsimp [d]; linarith
    have hCut1 := (hCutRange r).2
    have hCut0 := (hCutRange r).1
    have hMult :
        |r * cutoff (r / R)| ≤ d := by
      rw [abs_of_nonneg (mul_nonneg hr.le hCut0)]
      calc
        r * cutoff (r / R) ≤ r * 1 :=
          mul_le_mul_of_nonneg_left hCut1 hr.le
        _ = r := mul_one _
        _ ≤ d := by dsimp [d]; linarith
    have hdPow : d ≤ d ^ (7 / 4 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hdOne
        (show (1 : ℝ) ≤ 7 / 4 by norm_num)
      simpa only [Real.rpow_one] using h
    have hWeighted :
        d ^ (7 / 4 : ℝ) * ‖F r‖ ≤
          K * ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ)) :=
      actual_Hartree_physical_full_interaction_weighted_pointwise
        ell c r B A hell hellOne hc hr hB hA z hz hSup hStrauss
    calc
      ‖G r‖ = |r * cutoff (r / R)| * ‖F r‖ := by
        dsimp only [G,actualHartreeRadiallyConjugatedExteriorSource]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ d ^ (7 / 4 : ℝ) * ‖F r‖ :=
        mul_le_mul_of_nonneg_right (hMult.trans hdPow) (norm_nonneg _)
      _ ≤ K * ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ)) := hWeighted
  exact actual_Hartree_eighth_weighted_source_L2_of_pointwise
    (fun r : ℝ => ‖G r‖) ell K hell hK hG.norm
    (fun _ _ => norm_nonneg _) hPoint

end HBL.TypeIIDynamicSelection
