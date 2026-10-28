import HBL.WeightedPhaseFredholmInverse
import HBL.WeightedSourceChargeBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-!
# Identify the actual H-minus resonance in the weighted phase Hilbert space

The first angular sine mode is not a placeholder: pointwise it is exactly
twice the physical radial phase zero mode after the endpoint conjugation
q ↦ (1+r²)^(-1) q.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The physical phase zero mode, conjugated by the endpoint weight. -/
def weightedPhaseResonance (r : ℝ) : ℝ :=
  resonanceMinus r * affineJapaneseDecay 2 r

theorem firstSineMode_eq_twice_weightedPhaseResonance (r : ℝ) :
    weightedHartreeSineMode 1 r = 2 * weightedPhaseResonance r := by
  have hq : 0 < 1 + r ^ 2 := by positivity
  have hs : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  unfold weightedHartreeSineMode weightedPhaseResonance
  rw [resonanceMinus_def, affineJapaneseDecay_two]
  simp only [Nat.cast_one, mul_one]
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  unfold bubble
  rw [Real.sq_sqrt hq.le]
  field_simp [hs]
  rw [Real.sq_sqrt hq.le]
  ring

/-- The weighted phase generator, as an actual element of half-line L2. -/
def weightedPhaseResonanceL2 : RealL2 halfLineMeasure :=
  (1 / 2 : ℝ) • weightedHartreeSineModeL2 1

theorem weightedPhaseResonanceL2_ae :
    (weightedPhaseResonanceL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      weightedPhaseResonance := by
  filter_upwards [
    Lp.coeFn_smul (1 / 2 : ℝ) (weightedHartreeSineModeL2 1),
    weightedHartreeSineModeL2_ae 1] with r hsmul hmode
  unfold weightedPhaseResonanceL2
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmode, firstSineMode_eq_twice_weightedPhaseResonance]
  ring

theorem weightedPhaseResonanceL2_ne_zero :
    weightedPhaseResonanceL2 ≠ 0 := by
  unfold weightedPhaseResonanceL2
  exact smul_ne_zero (by norm_num) (weightedHartreeSineModeL2_ne_zero 1 (by omega))

theorem phaseFredholmSource_orthogonal_iff
    (F : RealL2 halfLineMeasure) :
    inner ℝ (weightedHartreeSineModeL2 1) F = 0 ↔
      inner ℝ weightedPhaseResonanceL2 F = 0 := by
  unfold weightedPhaseResonanceL2
  rw [real_inner_smul_left]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have hs : (1 / 2 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h).resolve_left hs

#print axioms firstSineMode_eq_twice_weightedPhaseResonance
#print axioms weightedPhaseResonanceL2_ae
#print axioms weightedPhaseResonanceL2_ne_zero
#print axioms phaseFredholmSource_orthogonal_iff

end HBL.Modulation.Monopole
