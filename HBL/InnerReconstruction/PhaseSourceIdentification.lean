import HBL.InnerReconstruction.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

def reconstructedPhaseSource (q F : ℝ → ℝ) (r : ℝ) : ℝ :=
  F r + 3 * weightedGreenDecay r ^ 2 * q r

theorem phase_reconstructed_source_ae
    (x : RealL2 halfLineMeasure) (q : ℝ → ℝ)
    (hx : (x : ℝ → ℝ) =ᵐ[halfLineMeasure] fun r => weightedGreenDecay r * q r) :
    (fun r => weightedGreenDecay r * ((3 : ℝ) • x : RealL2 halfLineMeasure) r)
      =ᵐ[halfLineMeasure] fun r => 3 * weightedGreenDecay r ^ 2 * q r := by
  filter_upwards [Lp.coeFn_smul (3 : ℝ) x, hx] with r hsmul hx'
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hsmul, hx']
  ring
end HBL.Modulation.Monopole
