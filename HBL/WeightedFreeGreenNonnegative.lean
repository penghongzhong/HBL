import HBL.WeightedHartreeSquareIdentity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
Negative eigenvalue exclusion for the actual weighted free Green operator.

A product-L2 kernel estimate gives `‖G‖ ≤ π/4 < 1`.  For `G f = μ f`,
this yields `1 + μ > 0`; pairing the already proved operator identity
`H² (I + G) = 576 G` with `f` then proves `μ ≥ 0`.  All integral,
self-adjointness, and operator-identity inputs are proved for the actual
operators, with no spectral classification or positivity premise.
-/

noncomputable section

open Set MeasureTheory
open HBL.L2Kernel HBL.Modulation.AffineTail

namespace HBL.Modulation.Monopole

theorem freeGreenMajorant_le_half_cauchy (r : ℝ) :
    freeGreenMajorant r ≤ (1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ := by
  have hden : 0 < 1 + r ^ 2 := by positivity
  have habs : |r| ≤ (1 + r ^ 2) / 2 := by
    nlinarith [sq_nonneg (|r| - 1), sq_abs r]
  calc
    freeGreenMajorant r = |r| * (1 + r ^ 2)⁻¹ ^ 2 := rfl
    _ ≤ ((1 + r ^ 2) / 2) * (1 + r ^ 2)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right habs (sq_nonneg _)
    _ = (1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ := by
      field_simp

theorem freeGreenMajorant_integral_le_pi_quarter :
    (∫ r, freeGreenMajorant r ∂halfLineMeasure) ≤ Real.pi / 4 := by
  have hm : Integrable freeGreenMajorant halfLineMeasure :=
    freeGreenMajorant_integrable.integrableOn
  have hc : Integrable (fun r : ℝ => (1 / 2 : ℝ) * (1 + r ^ 2)⁻¹)
      halfLineMeasure := integrable_inv_one_add_sq.integrableOn.const_mul _
  calc
    (∫ r, freeGreenMajorant r ∂halfLineMeasure) ≤
        ∫ r, (1 / 2 : ℝ) * (1 + r ^ 2)⁻¹ ∂halfLineMeasure :=
      integral_mono hm hc freeGreenMajorant_le_half_cauchy
    _ = Real.pi / 4 := by
      rw [integral_const_mul]
      change (1 / 2 : ℝ) * (∫ r in Ioi (0 : ℝ), (1 + r ^ 2)⁻¹) = _
      rw [integral_Ioi_inv_one_add_sq]
      simp only [Real.arctan_zero, sub_zero]
      ring

theorem weightedFreeGreenL2_norm_le_pi_quarter :
    ‖weightedFreeGreenL2‖ ≤ Real.pi / 4 := by
  have hnorm : ‖weightedFreeGreenL2‖ ^ 2 =
      ∫ p : ℝ × ℝ, weightedFreeGreen p.1 p.2 ^ 2
        ∂halfLineMeasure.prod halfLineMeasure := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [weightedFreeGreenL2_ae] with p hp
    rw [hp, Real.inner_apply]
    simp only [Function.uncurry, pow_two]
  have hm : Integrable freeGreenMajorant halfLineMeasure :=
    freeGreenMajorant_integrable.integrableOn
  have hpos : ∀ᵐ p : ℝ × ℝ ∂halfLineMeasure.prod halfLineMeasure,
      0 < p.1 ∧ 0 < p.2 := by
    rw [halfLineMeasure, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hsq : ‖weightedFreeGreenL2‖ ^ 2 ≤
      (∫ r, freeGreenMajorant r ∂halfLineMeasure) ^ 2 := by
    calc
      ‖weightedFreeGreenL2‖ ^ 2 =
          ∫ p : ℝ × ℝ, weightedFreeGreen p.1 p.2 ^ 2
            ∂halfLineMeasure.prod halfLineMeasure := hnorm
      _ ≤ ∫ p : ℝ × ℝ, freeGreenMajorant p.1 * freeGreenMajorant p.2
            ∂halfLineMeasure.prod halfLineMeasure := by
        apply integral_mono_ae weightedFreeGreen_sq_integrable (hm.mul_prod hm)
        filter_upwards [hpos] with p hp
        exact weightedFreeGreen_sq_le_majorant hp.1 hp.2
      _ = (∫ r, freeGreenMajorant r ∂halfLineMeasure) ^ 2 := by
        rw [integral_prod_mul]
        ring
  have hint0 : 0 ≤ ∫ r, freeGreenMajorant r ∂halfLineMeasure :=
    integral_nonneg freeGreenMajorant_nonneg
  have hnorm0 := norm_nonneg weightedFreeGreenL2
  have hpi := Real.pi_pos
  have hint := freeGreenMajorant_integral_le_pi_quarter
  nlinarith

theorem weightedFreeGreenOperator_norm_le_pi_quarter :
    ‖weightedFreeGreenOperator‖ ≤ Real.pi / 4 :=
  (HBL.L2Kernel.operator_norm_le weightedFreeGreenL2).trans weightedFreeGreenL2_norm_le_pi_quarter

theorem weightedFreeGreenOperator_norm_lt_one :
    ‖weightedFreeGreenOperator‖ < 1 := by
  have h := weightedFreeGreenOperator_norm_le_pi_quarter
  have hpi := Real.pi_lt_four
  linarith

theorem weightedFreeGreen_eigenvalue_nonneg (μ : ℝ) (f : RealL2 halfLineMeasure)
    (hf : f ≠ 0) (heigen : weightedFreeGreenOperator f = μ • f) :
    0 ≤ μ := by
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hnorm := weightedFreeGreenOperator.le_opNorm f
  rw [heigen, norm_smul, Real.norm_eq_abs] at hnorm
  have habs : |μ| ≤ ‖weightedFreeGreenOperator‖ := by nlinarith
  have hμ : -1 < μ := by
    have hbound := weightedFreeGreenOperator_norm_lt_one
    have hlower := neg_abs_le μ
    linarith
  have hT : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedHartreeOperator u) v =
        inner ℝ u (weightedHartreeOperator v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedHartreeOperator_selfAdjoint
  have hs := weightedHartreeSquareGreenIdentity f
  simp only [heigen, map_add, map_smul, smul_smul] at hs
  have hi := congrArg (fun z => inner ℝ z f) hs
  have hpair : inner ℝ
      (weightedHartreeOperator (weightedHartreeOperator f)) f =
      ‖weightedHartreeOperator f‖ ^ 2 :=
    (hT (weightedHartreeOperator f) f).trans (real_inner_self_eq_norm_sq _)
  simp only [inner_add_left, real_inner_smul_left, hpair,
    real_inner_self_eq_norm_sq] at hi
  have hleft : 0 ≤ (1 + μ) * ‖weightedHartreeOperator f‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hf2 : 0 < ‖f‖ ^ 2 := pow_pos hfpos 2
  by_contra! hneg
  have hright : (576 * μ) * ‖f‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hf2
  nlinarith

theorem weightedFreeGreen_nonzero_eigenvalue_pos (μ : ℝ) (f : RealL2 halfLineMeasure)
    (hf : f ≠ 0) (hμ : μ ≠ 0)
    (heigen : weightedFreeGreenOperator f = μ • f) :
    0 < μ := lt_of_le_of_ne (weightedFreeGreen_eigenvalue_nonneg μ f hf heigen) (Ne.symm hμ)

/-- A negative scalar has only the zero Green eigenvector. -/
theorem weightedFreeGreen_negative_eigenvector_eq_zero
    {μ : ℝ} (hμ : μ < 0) (f : RealL2 halfLineMeasure)
    (heigen : weightedFreeGreenOperator f = μ • f) : f = 0 := by
  by_contra hf
  exact (not_le_of_gt hμ) (weightedFreeGreen_eigenvalue_nonneg μ f hf heigen)

/-- No negative real number belongs to the actual Green operator spectrum. -/
theorem weightedFreeGreen_negative_not_mem_spectrum
    {μ : ℝ} (hμ : μ < 0) :
    μ ∉ spectrum ℝ weightedFreeGreenOperator := by
  intro hspec
  have heig := (weightedFreeGreenOperator_compact.hasEigenvalue_iff_mem_spectrum
    hμ.ne).mpr hspec
  obtain ⟨f, hf⟩ := heig.exists_hasEigenvector
  exact hf.2 (weightedFreeGreen_negative_eigenvector_eq_zero hμ f hf.apply_eq_smul)

/-- The real spectrum of the weighted free Green operator is nonnegative. -/
theorem weightedFreeGreen_spectrum_subset_nonnegative :
    spectrum ℝ weightedFreeGreenOperator ⊆ Ici (0 : ℝ) := by
  intro μ hμ
  by_contra hneg
  exact weightedFreeGreen_negative_not_mem_spectrum (lt_of_not_ge hneg) hμ

end HBL.Modulation.Monopole
