import HBL.WeightedPlusAffineComplete
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem hPlusAffineSource_continuous :
    Continuous (channelAffineSource HartreeChannel.plus) := by
  have hlocal : Continuous (hPlusLocalApply model) := by
    have hid : hPlusLocalApply model = fun r =>
        3 * channelAffineSource HartreeChannel.minus r +
        2 * affineModelSecondDerivative r := funext hPlusLocalAffineSource_identity
    rw [hid]
    exact (phaseAffineSource_continuous.const_mul 3).add
      (affineModelSecondDerivative_continuous.const_mul 2)
  exact hlocal.sub nonlocalAffine_continuous
end HBL.Modulation.Monopole
