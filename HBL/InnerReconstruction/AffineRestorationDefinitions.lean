import HBL.InnerReconstruction.RepresentativeProperties
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

def affineRestore (q : ℝ → ℝ) (a : ℝ) (r : ℝ) : ℝ := q r + a * model r

def InnerAffineProperties (u : ℝ → ℝ) (a : ℝ) : Prop :=
  Continuous u ∧ u 0 = 0 ∧
  (∀ tau : ℝ, 3 / 2 < tau → InWeightedL2 (-tau) u) ∧
  ∃ d : ℝ, Tendsto (fun r => u r - a * r) atTop (𝓝 d)
end HBL.Modulation.Monopole
