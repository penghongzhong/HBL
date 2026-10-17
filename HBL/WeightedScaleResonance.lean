import HBL.AffineTailLemmaClosed
import HBL.WeightedHartreeBirmanSchwinger

/-!
The actual weighted L2 representative of the real-channel scale resonance.

This file also records the Hilbert-space pairing identity that turns the
Fredholm cokernel condition for the weighted Birman--Schwinger equation into
the original threshold resonance pairing.  The fixed-vector premise is kept
explicit until the differential/nonlocal `H_+` equation is bridged to the
integral equation.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The paper's weighted scale resonance `x0 = (1+r²)⁻¹ ψ₊`. -/
def weightedScaleResonance (r : ℝ) : ℝ :=
  resonancePlus r * affineJapaneseDecay 2 r

theorem affineJapaneseDecay_two (r : ℝ) :
    affineJapaneseDecay 2 r = (1 + r ^ 2)⁻¹ := by
  unfold affineJapaneseDecay
  norm_num
  exact Real.rpow_neg_one (1 + r ^ 2)

theorem weightedScaleResonance_closed (r : ℝ) :
    weightedScaleResonance r = (1 + r ^ 2)⁻¹ * resonancePlus r := by
  unfold weightedScaleResonance
  rw [affineJapaneseDecay_two]
  ring

theorem weightedScaleResonance_continuous :
    Continuous weightedScaleResonance := by
  unfold weightedScaleResonance
  exact resonancePlus_contDiff_infty.continuous.mul
    (affineJapaneseDecay_continuous 2)

theorem weightedScaleResonance_memLp_two :
    MemLp weightedScaleResonance 2 halfLineMeasure := by
  apply (memLp_two_iff_integrable_sq
    weightedScaleResonance_continuous.aestronglyMeasurable).2
  rw [halfLineMeasure]
  refine integrable_inv_one_add_sq.integrableOn.mono'
    (weightedScaleResonance_continuous.pow 2).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    weightedScaleResonance_closed]
  have ha0 : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  have ha1 : (1 + r ^ 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
      (by nlinarith [sq_nonneg r])
  have hpsiAbs : |resonancePlus r| ≤ 1 :=
    (resonancePlus_abs_le_half r hr.le).trans (by norm_num)
  have hpsiSq : resonancePlus r ^ 2 ≤ 1 := by
    have hbounds := abs_le.mp hpsiAbs
    nlinarith
  calc
    ((1 + r ^ 2)⁻¹ * resonancePlus r) ^ 2 =
        (1 + r ^ 2)⁻¹ ^ 2 * resonancePlus r ^ 2 := by ring
    _ ≤ (1 + r ^ 2)⁻¹ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hpsiSq (sq_nonneg _)
    _ ≤ (1 + r ^ 2)⁻¹ := by nlinarith

/-- The actual half-line L2 vector denoted by `x0` in the manuscript. -/
def weightedScaleResonanceL2 : RealL2 halfLineMeasure :=
  weightedScaleResonance_memLp_two.toLp weightedScaleResonance

theorem weightedScaleResonanceL2_ae :
    (weightedScaleResonanceL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedScaleResonance :=
  weightedScaleResonance_memLp_two.coeFn_toLp

/-- If a weighted vector is fixed by the actual Birman--Schwinger operator,
then testing a Green-generated right-hand side against its cokernel generator
is exactly the original Hilbert-space resonance pairing. -/
theorem weightedBirmanSchwinger_cokernel_pairing
    (x0 F : RealL2 halfLineMeasure)
    (hx0 : weightedBirmanSchwingerOperator x0 = x0) :
    inner ℝ (weightedPotentialOperator x0) (weightedFreeGreenOperator F) =
      inner ℝ x0 F := by
  have hGP : weightedFreeGreenOperator (weightedPotentialOperator x0) = x0 := by
    simpa only [weightedBirmanSchwingerOperator,
      ContinuousLinearMap.comp_apply] using hx0
  calc
    inner ℝ (weightedPotentialOperator x0) (weightedFreeGreenOperator F) =
        inner ℝ (weightedFreeGreenOperator (weightedPotentialOperator x0)) F :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        weightedFreeGreenOperator_selfAdjoint (weightedPotentialOperator x0) F).symm
    _ = inner ℝ x0 F := by rw [hGP]

end HBL.Modulation.Monopole
