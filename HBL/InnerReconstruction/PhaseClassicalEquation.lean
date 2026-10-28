import HBL.InnerReconstruction.PhaseRepresentative
import HBL.InnerReconstruction.RepresentativeContinuous
import HBL.InnerReconstruction.RepresentativeIntegralEquation
import HBL.InnerReconstruction.PhaseSourceIdentification
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

theorem phase_innerGreenRepresentative_classical
    (x : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hcF : Continuous F)
    (heq : (1 - weightedPhaseBirman) x =
      weightedSourceGreenOperator sigma hsigma (weightedSourceDataL2 sigma F hF)) :
    let q := innerGreenRepresentative ((3 : ℝ) • x) F
    ∀ r : ℝ, 0 < r →
      HasDerivAt q (halfLineGreenTail (reconstructedPhaseSource q F) r) r ∧
      HasDerivAt (deriv q) (-reconstructedPhaseSource q F r) r ∧
      hMinusApply q r = F r := by
  let q := innerGreenRepresentative ((3 : ℝ) • x) F
  have hx := phase_innerGreenRepresentative_ae x sigma hsigma F hF heq
  have hq : Continuous q := innerGreenRepresentative_continuous _ sigma (by linarith) F hF
  have hcS : Continuous (reconstructedPhaseSource q F) :=
    hcF.add (((weightedGreenDecay_continuous.pow 2).const_mul 3).mul hq)
  have hsource : (fun r => weightedGreenDecay r * ((3 : ℝ) • x : RealL2 halfLineMeasure) r + F r)
      =ᵐ[halfLineMeasure] reconstructedPhaseSource q F := by
    filter_upwards [phase_reconstructed_source_ae x q hx] with r hr
    rw [hr]
    unfold reconstructedPhaseSource
    ring
  have hiS : Integrable (reconstructedPhaseSource q F) halfLineMeasure :=
    ((weightedGreen_source_integrable ((3 : ℝ) • x)).add
      (weightedSource_integrable sigma (by linarith) F hF)).congr hsource
  have hrep : q = halfLineMinGreen (reconstructedPhaseSource q F) := by
    funext r
    rw [show q r = halfLineMinGreen
        (fun rho => weightedGreenDecay rho * ((3 : ℝ) • x : RealL2 halfLineMeasure) rho + F rho) r from
      innerGreenRepresentative_eq_totalGreen _ sigma (by linarith) F hF r]
    unfold halfLineMinGreen
    apply integral_congr_ae
    filter_upwards [hsource] with rho h
    rw [h]
  dsimp only
  intro r hr
  have hD : HasDerivAt q (halfLineGreenTail (reconstructedPhaseSource q F) r) r := by
    apply (halfLineMinGreen_hasDerivAt hcS hiS hr).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => congrFun hrep t)
  have hDD : HasDerivAt (deriv q) (-reconstructedPhaseSource q F r) r := by
    apply (halfLineMinGreen_second_hasDerivAt hcS hiS hr).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => congrFun (congrArg deriv hrep) t)
  refine ⟨hD, hDD, ?_⟩
  unfold hMinusApply
  rw [hDD.deriv]
  unfold reconstructedPhaseSource potential weightedGreenDecay
  field_simp [show (1 + r ^ 2 : ℝ) ≠ 0 by positivity]
  ring
end HBL.Modulation.Monopole
