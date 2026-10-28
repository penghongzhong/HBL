import HBL.InnerDerivatives.PlusDerivativeWeightedDifference
import HBL.InnerDerivatives.MinusDerivativeWeightedDifference
import HBL.InnerDerivatives.PlusOutputDerivativeTail
import HBL.InnerDerivatives.MinusOutputDerivativeTail
import HBL.InnerDerivatives.PlusOutputSecondBound
import HBL.InnerDerivatives.MinusOutputSecondBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

/-- Fixed-weight derivative bounds for a classical affine output and its normalized remainder. -/
def InnerDerivativeEstimates (sigma beta C1 C2 Ct : ℝ) (F u q : ℝ → ℝ) (a : ℝ) : Prop :=
  InWeightedL2 beta (deriv q) ∧
  innerWeightedNorm beta (deriv q) ≤ C1 * innerWeightedNorm sigma F ∧
  InWeightedL2 sigma (deriv (deriv u)) ∧
  innerWeightedNorm sigma (deriv (deriv u)) ≤ C2 * innerWeightedNorm sigma F ∧
  (∀ r : ℝ, 2 < r → (1 + r) * ‖deriv u r - a‖ ≤ Ct * innerWeightedNorm sigma F) ∧
  Tendsto (deriv u) atTop (𝓝 a)

theorem exists_actualInner_derivative_estimates
    (sigma beta : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) (hbeta : beta < 1 / 2) :
    ∃ Cp1 Cm1 Cp2 Cm2 Cpt Cmt : ℝ,
      0 ≤ Cp1 ∧ 0 ≤ Cm1 ∧ 0 ≤ Cp2 ∧ 0 ≤ Cm2 ∧ 0 ≤ Cpt ∧ 0 ≤ Cmt ∧
      ∀ (F : ℝ → ℝ) (hF : InWeightedL2 sigma F), Continuous F →
        InnerDerivativeEstimates sigma beta Cp1 Cp2 Cpt F
          (normalizedPlusOutput sigma hLower hUpper F hF)
          (normalizedPlusRemainder sigma hLower hUpper F hF) (actualPlusCharge F) ∧
        InnerDerivativeEstimates sigma beta Cm1 Cm2 Cmt F
          (normalizedMinusOutput sigma hLower hUpper F hF)
          (normalizedMinusRemainder sigma hLower hUpper F hF) (actualMinusCharge F) := by
  refine ⟨innerDecayNorm (1 - beta) (by linarith) * innerPlusDerivativeConstant sigma hLower hUpper,
    innerDecayNorm (1 - beta) (by linarith) * innerMinusDerivativeConstant sigma hLower hUpper,
    innerPlusOutputSecondConstant sigma hLower hUpper, innerMinusOutputSecondConstant sigma hLower hUpper,
    innerPlusDerivativeConstant sigma hLower hUpper, innerMinusDerivativeConstant sigma hLower hUpper,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold innerPlusDerivativeConstant innerGreenDerivativeMajorant innerGreenMajorantNorm
      innerPlusHilbertConstant innerPlusCorrectionConstant innerSourceDerivativeMajorant innerMomentNorm innerDecayNorm
    positivity
  · unfold innerMinusDerivativeConstant innerGreenDerivativeMajorant innerGreenMajorantNorm
      innerMinusHilbertConstant innerMinusCorrectionConstant innerSourceDerivativeMajorant innerMomentNorm innerDecayNorm
    positivity
  · unfold innerPlusOutputSecondConstant innerPlusSecondDerivativeConstant innerPlusHilbertConstant innerPlusCorrectionConstant innerWeightedNorm
    positivity
  · unfold innerMinusOutputSecondConstant innerMinusSecondDerivativeConstant innerMinusHilbertConstant innerMinusCorrectionConstant innerWeightedNorm
    positivity
  · unfold innerPlusDerivativeConstant innerGreenDerivativeMajorant innerGreenMajorantNorm
      innerPlusHilbertConstant innerPlusCorrectionConstant innerSourceDerivativeMajorant innerMomentNorm innerDecayNorm
    positivity
  · unfold innerMinusDerivativeConstant innerGreenDerivativeMajorant innerGreenMajorantNorm
      innerMinusHilbertConstant innerMinusCorrectionConstant innerSourceDerivativeMajorant innerMomentNorm innerDecayNorm
    positivity
  · intro F hF hcF
    have hp1 := normalizedPlusRemainder_derivative_weighted sigma beta hLower hUpper hbeta F hF hcF
    have hm1 := normalizedMinusRemainder_derivative_weighted sigma beta hLower hUpper hbeta F hF hcF
    have hp2 := normalizedPlusOutput_second_derivative_bound sigma hLower hUpper F hF hcF
    have hm2 := normalizedMinusOutput_second_derivative_bound sigma hLower hUpper F hF hcF
    have hpt := normalizedPlusOutput_derivative_tail sigma hLower hUpper F hF hcF
    have hmt := normalizedMinusOutput_derivative_tail sigma hLower hUpper F hF hcF
    exact ⟨⟨hp1.1, hp1.2, hp2.1, hp2.2, hpt⟩, ⟨hm1.1, hm1.2, hm2.1, hm2.2, hmt⟩⟩
end HBL.Modulation.Monopole
