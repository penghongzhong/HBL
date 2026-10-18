import HBL.MonopoleWeightedSource
import HBL.WeightedHartreeSquareIdentity
import HBL.FredholmCokernelAlternative

/-!
Fredholm construction of the normalized first monopole correction.

All ingredients are concrete: the weighted datum is an actual `L²` vector,
the Birman--Schwinger operator is compact, and its adjoint kernel has already
been identified unconditionally.  Thus the threshold charge proved in
`MonopoleFredholmSource` is exactly the range condition for `I-K`.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem weightedScaleResonance_inner_monopoleDatum (ell : ℝ) :
    inner ℝ weightedScaleResonanceL2 (weightedMonopoleDatumL2 ell) =
      ∫ r in Ioi (0 : ℝ),
        resonancePlus r * monopoleCorrectedSource ell r := by
  rw [L2.inner_def]
  change (∫ r : ℝ,
      inner ℝ (weightedScaleResonanceL2 r)
        (weightedMonopoleDatumL2 ell r) ∂halfLineMeasure) =
    ∫ r : ℝ,
      resonancePlus r * monopoleCorrectedSource ell r
        ∂halfLineMeasure
  apply integral_congr_ae
  filter_upwards [weightedScaleResonanceL2_ae,
    weightedMonopoleDatumL2_ae ell] with r hx0 hF
  rw [hx0, hF, Real.inner_apply]
  unfold weightedScaleResonance weightedMonopoleDatum
    affineJapaneseDecay
  norm_num
  rw [Real.rpow_neg_one (1 + r ^ 2)]
  field_simp [show 1 + r ^ 2 ≠ 0 by positivity]

theorem weightedScaleResonance_inner_monopoleDatum_zero :
    inner ℝ weightedScaleResonanceL2
      (weightedMonopoleDatumL2 monopoleAffineSlope) = 0 := by
  rw [weightedScaleResonance_inner_monopoleDatum]
  exact monopole_corrected_source_orthogonal

/-- The Green-generated right-hand side in the concrete
Birman--Schwinger equation. -/
def monopoleFredholmRightHandSide : RealL2 halfLineMeasure :=
  weightedFreeGreenOperator
    (weightedMonopoleDatumL2 monopoleAffineSlope)

theorem monopoleFredholmRightHandSide_cokernel_inner_zero :
    inner ℝ (weightedPotentialOperator weightedScaleResonanceL2)
      monopoleFredholmRightHandSide = 0 := by
  unfold monopoleFredholmRightHandSide
  rw [weightedScaleResonance_cokernel_pairing]
  exact weightedScaleResonance_inner_monopoleDatum_zero

theorem adjoint_one_sub_weightedBirmanSchwinger_kernel :
    (ContinuousLinearMap.adjoint
      (1 - weightedBirmanSchwingerOperator)).ker =
        Submodule.span ℝ
          {weightedPotentialOperator weightedScaleResonanceL2} := by
  calc
    (ContinuousLinearMap.adjoint
      (1 - weightedBirmanSchwingerOperator)).ker =
        (ContinuousLinearMap.id ℝ (RealL2 halfLineMeasure) -
          ContinuousLinearMap.adjoint
            weightedBirmanSchwingerOperator).ker := by
      congr 1
      simp only [sub_eq_add_neg]
      simp
      rw [ContinuousLinearMap.adjoint_one,
        ContinuousLinearMap.one_def]
    _ = Submodule.span ℝ
          {weightedPotentialOperator weightedScaleResonanceL2} :=
      weightedBirmanSchwinger_adjointKernel_eq_scale_span

theorem monopoleFredholmRightHandSide_mem_adjointKernel_orthogonal :
    monopoleFredholmRightHandSide ∈
      (ContinuousLinearMap.adjoint
        (1 - weightedBirmanSchwingerOperator)).kerᗮ := by
  rw [adjoint_one_sub_weightedBirmanSchwinger_kernel,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact monopoleFredholmRightHandSide_cokernel_inner_zero

/-- Existence and uniqueness after imposing the canonical Hilbert-space
normalization perpendicular to the Birman--Schwinger fixed space. -/
theorem existsUnique_monopoleFredholmSolution :
    ∃! x : (1 - weightedBirmanSchwingerOperator).kerᗮ,
      (1 - weightedBirmanSchwingerOperator) (x : RealL2 halfLineMeasure) =
        monopoleFredholmRightHandSide :=
  HBL.Fredholm.existsUnique_one_sub_apply_eq_of_mem_adjointKernel_orthogonal
    weightedBirmanSchwingerOperator_compact
    monopoleFredholmRightHandSide_mem_adjointKernel_orthogonal

/-- The uniquely normalized weighted correction. -/
def monopoleFredholmSolution :
    (1 - weightedBirmanSchwingerOperator).kerᗮ :=
  Classical.choose existsUnique_monopoleFredholmSolution

theorem monopoleFredholmSolution_equation :
    (1 - weightedBirmanSchwingerOperator)
        (monopoleFredholmSolution : RealL2 halfLineMeasure) =
      monopoleFredholmRightHandSide :=
  (Classical.choose_spec existsUnique_monopoleFredholmSolution).1

theorem monopoleFredholmSolution_unique
    (x : (1 - weightedBirmanSchwingerOperator).kerᗮ)
    (hx : (1 - weightedBirmanSchwingerOperator)
        (x : RealL2 halfLineMeasure) = monopoleFredholmRightHandSide) :
    x = monopoleFredholmSolution := by
  exact (Classical.choose_spec existsUnique_monopoleFredholmSolution).2 x hx

theorem monopoleFredholmSolution_eq_green :
    (monopoleFredholmSolution : RealL2 halfLineMeasure) =
      weightedFreeGreenOperator
        (weightedPotentialOperator
            (monopoleFredholmSolution : RealL2 halfLineMeasure) +
          weightedMonopoleDatumL2 monopoleAffineSlope) := by
  have heq := monopoleFredholmSolution_equation
  unfold monopoleFredholmRightHandSide at heq
  change (monopoleFredholmSolution : RealL2 halfLineMeasure) -
      weightedBirmanSchwingerOperator
        (monopoleFredholmSolution : RealL2 halfLineMeasure) =
      weightedFreeGreenOperator
        (weightedMonopoleDatumL2 monopoleAffineSlope) at heq
  unfold weightedBirmanSchwingerOperator at heq
  rw [ContinuousLinearMap.comp_apply] at heq
  rw [map_add]
  have hsum := (sub_eq_iff_eq_add).mp heq
  simpa only [add_comm] using hsum

end HBL.Modulation.Monopole
