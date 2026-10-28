import HBL.InnerReconstruction.PlusRepresentative
import HBL.InnerReconstruction.RepresentativeContinuous
import HBL.InnerReconstruction.RepresentativeIntegralEquation
import HBL.InnerReconstruction.PlusSourceIdentification
import HBL.WeightedHartreePointwiseContinuous
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem plus_innerGreenRepresentative_classical
    (x : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F)
    (heq : (1 - weightedBirmanSchwingerOperator) x =
      weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF)) :
    let q := innerGreenRepresentative (weightedPotentialOperator x) F
    ∀ r : ℝ, 0 < r →
      HasDerivAt q (halfLineGreenTail (reconstructedPlusSource q F) r) r ∧
      HasDerivAt (deriv q) (-reconstructedPlusSource q F r) r ∧
      hPlusApply q r = F r := by
  let q := innerGreenRepresentative (weightedPotentialOperator x) F
  have hx := plus_innerGreenRepresentative_ae x sigma hsigma F hF heq
  have hq : Continuous q := innerGreenRepresentative_continuous _ sigma (by linarith) F hF
  have hmem : MemLp (fun r => weightedGreenDecay r * q r) 2 halfLineMeasure :=
    (Lp.memLp x).ae_eq hx
  have hcS : Continuous (reconstructedPlusSource q F) :=
    (hcF.add (((weightedGreenDecay_continuous.pow 2).const_mul 9).mul hq)).add
      (nonlocalApply_continuous_of_weighted_memLp q hmem)
  have hsource : (fun r => weightedGreenDecay r * weightedPotentialOperator x r + F r)
      =ᵐ[halfLineMeasure] reconstructedPlusSource q F := by
    filter_upwards [plus_reconstructed_source_ae x q hx] with r hr
    rw [hr]
    unfold reconstructedPlusSource
    ring
  have hiS : Integrable (reconstructedPlusSource q F) halfLineMeasure :=
    ((weightedGreen_source_integrable (weightedPotentialOperator x)).add
      (weightedSource_integrable sigma (by linarith) F hF)).congr hsource
  have hrep : q = halfLineMinGreen (reconstructedPlusSource q F) := by
    funext r
    rw [show q r = halfLineMinGreen
        (fun rho => weightedGreenDecay rho * weightedPotentialOperator x rho + F rho) r from
      innerGreenRepresentative_eq_totalGreen _ sigma (by linarith) F hF r]
    unfold halfLineMinGreen
    apply integral_congr_ae
    filter_upwards [hsource] with rho h
    rw [h]
  dsimp only
  intro r hr
  have hD : HasDerivAt q (halfLineGreenTail (reconstructedPlusSource q F) r) r := by
    apply (halfLineMinGreen_hasDerivAt hcS hiS hr).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => congrFun hrep t)
  have hDD : HasDerivAt (deriv q) (-reconstructedPlusSource q F r) r := by
    apply (halfLineMinGreen_second_hasDerivAt hcS hiS hr).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => congrFun (congrArg deriv hrep) t)
  refine ⟨hD, hDD, ?_⟩
  unfold hPlusApply
  rw [hDD.deriv]
  unfold reconstructedPlusSource potential weightedGreenDecay
  field_simp [show (1 + r ^ 2 : ℝ) ≠ 0 by positivity]
  ring
end HBL.Modulation.Monopole
