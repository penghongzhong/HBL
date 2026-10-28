import HBL.WeightedPlusAffineLocal
import HBL.WeightedPlusAffineNonlocal
import HBL.WeightedSourceFredholmSolution
import Mathlib.Tactic

/-!
# Actual full H-plus affine source in the manuscript weighted source class

This closes the source-space premise necessary to apply the genuine
H-plus Fredholm inverse after removing its uniquely forced affine charge.
The source is the full nonlocal physical operator, not a surrogate local
Schrodinger operator.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

open HBL.Modulation.Monopole

theorem hPlusAffineSource_inWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2) :
    InWeightedL2 sigma (channelAffineSource HartreeChannel.plus) := by
  have hl := hPlusLocalAffineSource_inWeightedL2 sigma hsigma
  have hn := nonlocalAffine_inWeightedL2 sigma hsigma
  unfold InWeightedL2 at hl hn ⊢
  have heq :
      (fun r : ℝ =>
          affineJapaneseWeight sigma r *
            channelAffineSource HartreeChannel.plus r) =
        (fun r : ℝ =>
          affineJapaneseWeight sigma r * hPlusLocalApply model r -
          affineJapaneseWeight sigma r * nonlocalApply model r) := by
    funext r
    change affineJapaneseWeight sigma r * hPlusApply model r =
      affineJapaneseWeight sigma r * hPlusLocalApply model r -
        affineJapaneseWeight sigma r * nonlocalApply model r
    rw [hPlusApply_eq_local_sub_nonlocal]
    ring
  rw [heq]
  exact hl.sub hn

theorem hPlusAffineCorrectedSource_inWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (alpha : ℝ) :
    InWeightedL2 sigma
      (fun r => F r - alpha * channelAffineSource HartreeChannel.plus r) := by
  have hq := hPlusAffineSource_inWeightedL2 sigma hsigma
  unfold InWeightedL2 at hF hq ⊢
  have h := hF.sub (hq.const_mul alpha)
  convert h using 1
  funext r
  simp only [Pi.sub_apply]
  ring

/-- Compatibility for the actual H-plus affine-corrected source.
The unique charge formula was already proved for either Hartree channel. -/
theorem hPlusAffineCorrectedSource_charge_zero
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    channelPairing HartreeChannel.plus
        (fun r => F r -
          (-(channelPairing HartreeChannel.plus F) /
              channelLimit HartreeChannel.plus) *
            channelAffineSource HartreeChannel.plus r) = 0 := by
  let alpha : ℝ :=
    -(channelPairing HartreeChannel.plus F) / channelLimit HartreeChannel.plus
  have horth : AffineTailOrthogonal HartreeChannel.plus F alpha :=
    (affineTailOrthogonal_iff_charge_formula
      HartreeChannel.plus sigma hsigma F hF alpha).2 rfl
  exact horth.2

#print axioms hPlusAffineSource_inWeightedL2
#print axioms hPlusAffineCorrectedSource_inWeightedL2
#print axioms hPlusAffineCorrectedSource_charge_zero

end HBL.Modulation.AffineTail
