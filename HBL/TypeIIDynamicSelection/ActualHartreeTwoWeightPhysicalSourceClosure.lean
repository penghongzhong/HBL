import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedInnerChargeGain
import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedExteriorL2

/-!
# Revised HBL 2.13: one original Hartree PDE source, two physical radial weights

This is the short, self-contained, actual-source counterpart of the
revised intermediate manuscript lemma. Its inputs are ONLY the original
physical radiation amplitude/Strauss bounds and scale/core range.
The full nonlocal core-radiation interaction is not truncated inside a
Riesz integral. q=r*u is conjugated correctly and exactly partitioned.

The inner source has the strong L^(2,7/4) source bound, true
O(ell^(1/16)) pointwise envelope, and two physically forced affine
resonance charges O(ell^(1/16)); the complementary outer conjugated
source is in the weaker L² and has a quantitative O(ell^(1/8)) bound.
Every output is obtained from the same actual source without assuming
a Kummer trace, a remote inverse, time order or a blowup rate.

The original 2.13 finite-profile/three-region C1 theorem remains OPEN.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- One completely physical two-weight radial Hartree source package.
All source memberships, integral bounds and affine charge gains are
conclusions.  No unrelated abstract region-solver assumptions. -/
theorem actual_Hartree_one_source_two_weight_conjugation_certificate
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let R := actualHartreeSlowInnerRadius ell
    let Gin := actualHartreeRadiallyConjugatedInnerSource R ell c z
    let Gout := actualHartreeRadiallyConjugatedExteriorSource R ell c z
    let K := actualHartreePhysicalWeightedSourceConstant B A
    let Q := (2 * K) * ell ^ (1 / 16 : ℝ) *
      actualHartreePhysicalChargeTailConstant
    (∀ r : ℝ,
      (r : ℂ) * actualHartreePhysicalSliceInteraction ell c z r =
        Gin r + Gout r) ∧
    (Measurable Gin ∧
      MemLp (fun r : ℝ => affineJapaneseWeight (7 / 4 : ℝ) r * ‖Gin r‖)
        2 halfLineMeasure ∧
      (∀ r : ℝ, 0 < r →
        affineJapaneseWeight (7 / 4 : ℝ) r * ‖Gin r‖ ≤
          (2 * K) * ell ^ (1 / 16 : ℝ) *
            (1 + r) ^ (-(5 / 8 : ℝ)))) ∧
    (MemLp (fun r : ℝ => ‖Gout r‖) 2 halfLineMeasure ∧
      (∫ r in Ioi (0 : ℝ), ‖Gout r‖ ^ 2) ≤
        (K * ell ^ (1 / 8 : ℝ)) ^ 2 *
          (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ)))) ∧
    (|actualPlusCharge (fun r => (Gin r).re)| ≤ 2 * Q ∧
      |actualMinusCharge (fun r => (Gin r).im)| ≤ Q) := by
  dsimp only
  let R : ℝ := actualHartreeSlowInnerRadius ell
  let Gin : ℝ → ℂ := actualHartreeRadiallyConjugatedInnerSource R ell c z
  let Gout : ℝ → ℂ := actualHartreeRadiallyConjugatedExteriorSource R ell c z
  have hIn := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hOut := actual_Hartree_conjugated_exterior_unweighted_L2
    R ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hCharge := actual_Hartree_conjugated_inner_forced_charges_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  refine ⟨?_, hIn, hOut, hCharge⟩
  intro r
  exact actual_Hartree_one_source_exact_inner_exterior_partition
    R ell c r z

end HBL.TypeIIDynamicSelection
