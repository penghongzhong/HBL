import HBL.MonopoleProfileEquation
import HBL.InnerReconstruction.AffineRestorationDefinitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem affineRestore_nonlocal (q : ℝ → ℝ) (a : ℝ)
    (hq : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure)
    {r : ℝ} (hr : 0 ≤ r) :
    nonlocalApply (affineRestore q a) r = nonlocalApply q r + a * nonlocalApply model r := by
  have hqint := nonlocalApply_integrable_of_weighted_memLp q hq hr
  have hmint := nonlocalApply_integrable_of_weighted_memLp model affineConjugatedModel_memLp_two hr
  unfold nonlocalApply
  have heq : (fun rho => hartreeKernel r rho * affineRestore q a rho) =
      fun rho => hartreeKernel r rho * q rho + a * (hartreeKernel r rho * model rho) := by
    funext rho
    unfold affineRestore
    ring
  rw [heq, integral_add hqint (hmint.const_mul a), integral_const_mul]
end HBL.Modulation.Monopole
