import HBL.InnerEstimates.PlusOutputBound
import HBL.InnerEstimates.MinusOutputBound
import HBL.InnerEstimates.PlusOutputClassical
import HBL.InnerEstimates.MinusOutputClassical
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

/-- Both actual classical affine inverses are bounded and Lipschitz from the
physical weighted source space to the requested weighted output space.
Constants depend on the two weights and the fixed actual operators, not on data. -/
theorem exists_actualInner_bounded_classical_solvers
    (sigma tau : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2) (htau : 3 / 2 < tau) :
    ∃ Cp Cm : ℝ, 0 ≤ Cp ∧ 0 ≤ Cm ∧
    (∀ (F : ℝ → ℝ) (hF : InWeightedL2 sigma F),
      InnerAffineProperties (normalizedPlusOutput sigma hLower hUpper F hF) (actualPlusCharge F) ∧
      InnerAffineProperties (normalizedMinusOutput sigma hLower hUpper F hF) (actualMinusCharge F) ∧
      innerWeightedNorm (-tau) (normalizedPlusOutput sigma hLower hUpper F hF) ≤ Cp * innerWeightedNorm sigma F ∧
      innerWeightedNorm (-tau) (normalizedMinusOutput sigma hLower hUpper F hF) ≤ Cm * innerWeightedNorm sigma F ∧
      (Continuous F → ∀ r : ℝ, 0 < r →
        hPlusApply (normalizedPlusOutput sigma hLower hUpper F hF) r = F r ∧
        hMinusApply (normalizedMinusOutput sigma hLower hUpper F hF) r = F r)) ∧
    (∀ (F G : ℝ → ℝ) (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G),
      innerWeightedNorm (-tau) (fun r => normalizedPlusOutput sigma hLower hUpper F hF r -
        normalizedPlusOutput sigma hLower hUpper G hG r) ≤ Cp * innerWeightedNorm sigma (fun r => F r - G r) ∧
      innerWeightedNorm (-tau) (fun r => normalizedMinusOutput sigma hLower hUpper F hF r -
        normalizedMinusOutput sigma hLower hUpper G hG r) ≤ Cm * innerWeightedNorm sigma (fun r => F r - G r)) := by
  refine ⟨innerPlusOutputConstant sigma tau hLower hUpper htau,
    innerMinusOutputConstant sigma tau hLower hUpper htau, ?_, ?_, ?_, ?_⟩
  · unfold innerPlusOutputConstant innerPlusRemainderConstant innerPlusHilbertConstant
      innerPlusCorrectionConstant innerDecayNorm innerGreenMajorantNorm innerMomentNorm innerWeightedNorm
    positivity
  · unfold innerMinusOutputConstant innerMinusRemainderConstant innerMinusHilbertConstant
      innerMinusCorrectionConstant innerDecayNorm innerGreenMajorantNorm innerMomentNorm innerWeightedNorm
    positivity
  · intro F hF
    refine ⟨normalizedPlusOutput_properties sigma hLower hUpper F hF,
      normalizedMinusOutput_properties sigma hLower hUpper F hF,
      normalizedPlusOutput_weighted_norm_le sigma tau hLower hUpper htau F hF,
      normalizedMinusOutput_weighted_norm_le sigma tau hLower hUpper htau F hF, ?_⟩
    intro hc r hr
    exact ⟨(normalizedPlusOutput_classical sigma hLower hUpper F hF hc r hr).2.2,
      (normalizedMinusOutput_classical sigma hLower hUpper F hF hc r hr).2.2⟩
  · intro F G hF hG
    rw [innerWeightedNorm_sub_eq sigma F G hF hG]
    exact ⟨normalizedPlusOutput_weighted_difference_le sigma tau hLower hUpper htau F G hF hG,
      normalizedMinusOutput_weighted_difference_le sigma tau hLower hUpper htau F G hF hG⟩
end HBL.Modulation.Monopole
