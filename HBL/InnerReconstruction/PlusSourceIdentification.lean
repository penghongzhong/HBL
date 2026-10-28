import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

def reconstructedPlusSource (q F : ℝ → ℝ) (r : ℝ) : ℝ :=
  F r + 9 * weightedGreenDecay r ^ 2 * q r + nonlocalApply q r

theorem plus_reconstructed_source_ae
    (x : RealL2 halfLineMeasure) (q : ℝ → ℝ)
    (hx : (x : ℝ → ℝ) =ᵐ[halfLineMeasure] fun r => weightedGreenDecay r * q r) :
    (fun r => weightedGreenDecay r * weightedPotentialOperator x r) =ᵐ[halfLineMeasure]
      fun r => 9 * weightedGreenDecay r ^ 2 * q r + nonlocalApply q r := by
  have hmem : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure :=
    (Lp.memLp x).ae_eq hx
  have hcast : hmem.toLp (fun r => weightedGreenDecay r * q r) = x := by
    apply Lp.ext
    exact hmem.coeFn_toLp.trans hx.symm
  have hconj (r : ℝ) : weightedHartreePointwise x r =
      (1 + r ^ 2) * nonlocalApply q r := by
    rw [← hcast]
    exact weightedHartreePointwise_conjugation q hmem r
  have hpot : weightedPotentialOperator x = (9 : ℝ) • x + weightedHartreeOperator x := rfl
  rw [hpot]
  filter_upwards [Lp.coeFn_add ((9 : ℝ) • x) (weightedHartreeOperator x),
    Lp.coeFn_smul (9 : ℝ) x, weightedHartreeOperator_ae_pointwise x, hx]
    with r hadd hsmul hhartree hx'
  simp only [Pi.add_apply] at hadd
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hadd, hsmul, hhartree, hx', hconj]
  unfold weightedGreenDecay
  field_simp [show (1 + r ^ 2 : ℝ) ≠ 0 by positivity]
end HBL.Modulation.Monopole
