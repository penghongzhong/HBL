import HBL.InnerReconstruction.PlusAffineSourceContinuous
import HBL.ActualInnerAffinelyCorrected
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem correctedPlusSource_continuous (F : ℝ → ℝ) (hF : Continuous F) :
    Continuous (HBL.Profile.ActualInner.correctedPlusSource F) :=
  hF.sub (hPlusAffineSource_continuous.const_mul
    (HBL.Profile.ActualInner.actualPlusCharge F))
end HBL.Modulation.Monopole
