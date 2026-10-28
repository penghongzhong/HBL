import HBL.InnerReconstruction.GreenLimit
import HBL.InnerReconstruction.FirstMoment
import HBL.InnerReconstruction.SourceIntegrable
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

def innerGreenTailConstant (g : RealL2 halfLineMeasure) (F : ℝ → ℝ) : ℝ :=
  (∫ rho, rho * (weightedGreenDecay rho * g rho) ∂halfLineMeasure) +
    ∫ rho, rho * F rho ∂halfLineMeasure

theorem innerGreenRepresentative_tendsto
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 3 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    Tendsto (innerGreenRepresentative g F) atTop (𝓝 (innerGreenTailConstant g F)) := by
  have hM : Integrable (fun rho : ℝ => rho * (weightedGreenDecay rho * g rho))
      halfLineMeasure := by
    refine (weightedGreenOutputMajorant_mul_integrable g).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    unfold weightedGreenOutputMajorant
    rw [abs_of_pos hrho]
    ring
  have hg := halfLineMinGreen_tendsto_firstMoment
    (fun rho => weightedGreenDecay rho * g rho) (weightedGreen_source_integrable g) hM
  have hsource := halfLineMinGreen_tendsto_firstMoment F
    (weightedSource_integrable sigma (by linarith) F hF)
    (weightedSource_firstMoment_integrable sigma hsigma F hF)
  exact hg.add hsource
end HBL.Modulation.Monopole
