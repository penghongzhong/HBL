import HBL.ActualInnerAffinelyCorrected
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem correctedMinusSource_continuous (F : ℝ → ℝ) (hF : Continuous F) :
    Continuous (HBL.Profile.ActualInner.correctedMinusSource F) :=
  hF.sub (phaseAffineSource_continuous.const_mul
    (HBL.Profile.ActualInner.actualMinusCharge F))
end HBL.Modulation.Monopole
