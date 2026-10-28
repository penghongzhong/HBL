import HBL.InnerReconstruction.RepresentativeWeightedOutput
import HBL.InnerReconstruction.RepresentativeZero
import HBL.InnerReconstruction.RepresentativeLimit
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Continuous, origin-normalized, bounded-tail output in every admissible decay weight. -/
def InnerRemainderProperties (q : ℝ → ℝ) : Prop :=
  Continuous q ∧ q 0 = 0 ∧
  (∀ tau : ℝ, 1 / 2 < tau → InWeightedL2 (-tau) q) ∧
  ∃ d : ℝ, Tendsto q atTop (𝓝 d)

theorem innerGreenRepresentative_properties
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    InnerRemainderProperties (innerGreenRepresentative g F) :=
  ⟨innerGreenRepresentative_continuous g sigma (by linarith) F hF,
   innerGreenRepresentative_zero g F,
   fun tau htau => innerGreenRepresentative_inWeightedL2_neg g sigma tau hsigma htau F hF,
   innerGreenTailConstant g F, innerGreenRepresentative_tendsto g sigma hsigma F hF⟩
end HBL.Modulation.Monopole
