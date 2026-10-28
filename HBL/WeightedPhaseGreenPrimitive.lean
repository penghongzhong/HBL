import HBL.WeightedPhaseZeroModeBridge
import HBL.WeightedGreenEigenClassification
import Mathlib.Tactic

/-!
# Exact phase Green primitive, without a new ODE solution hypothesis

The actual positive half-line free Green operator has a strict first-sine
eigenvector with eigenvalue 1/3.  We combine the proved a.e. integral
representative with the exact identity of that sine mode and psi_minus.
The result is the concrete unweighted Green primitive identity

  ∫_0^∞ min(r,rho) (1+r²)^(-1) phi_1(r) dr = (2/3) psi_minus(rho)

for a.e. rho>0.  This is the key input for passing the physical phase
threshold charge through the weighted cross-space Green operator.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedPhaseGreenPrimitive_ae :
    (fun rho : ℝ =>
      weightedGreenPrimitive (weightedHartreeSineModeL2 1) rho)
      =ᵐ[halfLineMeasure]
    (fun rho : ℝ => (2 / 3 : ℝ) * resonanceMinus rho) := by
  have heig :
      weightedFreeGreenOperator (weightedHartreeSineModeL2 1) =
        (1 / 3 : ℝ) • weightedHartreeSineModeL2 1 := by
    simpa only [Nat.cast_one, one_pow, mul_one] using
      (weightedFreeGreenOperator_sineMode 1 (by omega))
  have hpoint :=
    weightedFreeGreenOperator_ae_pointwise
      (weightedHartreeSineModeL2 1)
  rw [heig] at hpoint
  filter_upwards [hpoint,
    Lp.coeFn_smul (1 / 3 : ℝ) (weightedHartreeSineModeL2 1),
    weightedHartreeSineModeL2_ae 1] with rho hp hsmul hmode
  rw [hsmul, hmode] at hp
  simp only [Pi.smul_apply, smul_eq_mul] at hp
  rw [firstSineMode_eq_twice_weightedPhaseResonance] at hp
  unfold weightedPhaseResonance at hp
  rw [affineJapaneseDecay_two] at hp
  change (1 + rho ^ 2)⁻¹ *
      weightedGreenPrimitive (weightedHartreeSineModeL2 1) rho =
        (1 / 3 : ℝ) *
          (2 * (resonanceMinus rho * (1 + rho ^ 2)⁻¹)) at hp
  have hden : (1 + rho ^ 2)⁻¹ ≠ 0 := by positivity
  apply (mul_left_cancel₀ hden)
  calc
    (1 + rho ^ 2)⁻¹ *
        weightedGreenPrimitive (weightedHartreeSineModeL2 1) rho =
      (1 / 3 : ℝ) *
          (2 * (resonanceMinus rho * (1 + rho ^ 2)⁻¹)) := hp
    _ = (1 + rho ^ 2)⁻¹ *
      ((2 / 3 : ℝ) * resonanceMinus rho) := by ring

#print axioms weightedPhaseGreenPrimitive_ae

end HBL.Modulation.Monopole
