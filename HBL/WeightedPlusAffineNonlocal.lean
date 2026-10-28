import HBL.WeightedHartreePointwiseContinuous
import HBL.WeightedPhaseAffineSource
import Mathlib.Tactic

/-!
# Actual Hartree nonlocal affine forcing belongs to weighted L2

The affine cutoff model chi_aff(r)*r is unbounded, but its conjugate
(1+r^2)^(-1) chi_aff(r)*r belongs to the genuine half-line Hilbert space.

The previously verified pointwise kernel identity gives

    T((1+r²)^(-1) q) = (1+r²) nonlocalApply(q)

for the physical Hartree operator.  Since
<r>^sigma/(1+r²) <= 1 for sigma<=2, the actual nonlocal affine forcing
is in the manuscript L^(2,sigma) source class.  No auxiliary axiom,
abstract source predicate, or unproved kernel estimate is introduced.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

def affineConjugatedModel (r : ℝ) : ℝ :=
  weightedGreenDecay r * model r

theorem affineConjugatedModel_continuous :
    Continuous affineConjugatedModel :=
  weightedGreenDecay_continuous.mul model_contDiff_infty.continuous

theorem affineConjugatedModel_far (r : ℝ) (hr : 2 < r) :
    affineConjugatedModel r = r * (1 + r ^ 2)⁻¹ := by
  unfold affineConjugatedModel weightedGreenDecay
  rw [model_eq_id_of_two_le r hr.le]
  ring

theorem affineConjugatedModel_memLp_two :
    MemLp affineConjugatedModel 2 halfLineMeasure := by
  have hc := affineConjugatedModel_continuous
  have hcompact :
      IntegrableOn (fun r : ℝ => affineConjugatedModel r ^ 2)
        (Ioc (0 : ℝ) 2) :=
    (hc.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmajor :
      IntegrableOn (fun r : ℝ => (1 + r ^ 2)⁻¹) (Ioi 2) :=
    integrable_inv_one_add_sq.integrableOn
  have htail :
      IntegrableOn (fun r : ℝ => affineConjugatedModel r ^ 2) (Ioi 2) := by
    refine hmajor.mono' (hc.pow 2).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      affineConjugatedModel_far r hr]
    have hden : 1 + r ^ 2 ≠ 0 := by positivity
    have hbound : r ^ 2 ≤ 1 + r ^ 2 := by linarith
    calc
      (r * (1 + r ^ 2)⁻¹) ^ 2 =
          r ^ 2 * (1 + r ^ 2)⁻¹ ^ 2 := by ring
      _ ≤ (1 + r ^ 2) * (1 + r ^ 2)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
      _ = (1 + r ^ 2)⁻¹ := by field_simp [hden]
  have hall :
      IntegrableOn (fun r : ℝ => affineConjugatedModel r ^ 2) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
    exact hcompact.union htail
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable.restrict).2
  exact hall

def affineConjugatedModelL2 : RealL2 halfLineMeasure :=
  affineConjugatedModel_memLp_two.toLp affineConjugatedModel

theorem affineConjugatedModelL2_ae :
    (affineConjugatedModelL2 : ℝ → ℝ) =ᵐ[halfLineMeasure]
      affineConjugatedModel :=
  affineConjugatedModel_memLp_two.coeFn_toLp

theorem affineConjugatedModel_eq_input :
    (fun r : ℝ => weightedGreenDecay r * model r) = affineConjugatedModel :=
  rfl

theorem weightedHartreeAffine_physical_identity (r : ℝ) :
    weightedHartreePointwise affineConjugatedModelL2 r =
      (1 + r ^ 2) * nonlocalApply model r := by
  exact weightedHartreePointwise_conjugation
    model affineConjugatedModel_memLp_two r

theorem nonlocalAffine_continuous :
    Continuous (nonlocalApply model) :=
  nonlocalApply_continuous_of_weighted_memLp
    model affineConjugatedModel_memLp_two

/-- Actual nonlocal contribution to H_plus(chi_aff r) in the physical
weighted L2 range sigma<=2. -/
theorem nonlocalAffine_inWeightedL2
    (sigma : ℝ) (hsigma : sigma ≤ 2) :
    InWeightedL2 sigma (nonlocalApply model) := by
  let f : RealL2 halfLineMeasure := affineConjugatedModelL2
  have hy : MemLp (weightedHartreePointwise f) 2 halfLineMeasure :=
    (Lp.memLp (weightedHartreeOperator f)).ae_eq
      (weightedHartreeOperator_ae_pointwise f)
  have hc : Continuous
      (fun r : ℝ =>
        affineJapaneseWeight sigma r * nonlocalApply model r) :=
    (affineJapaneseWeight_continuous sigma).mul
      nonlocalAffine_continuous
  unfold InWeightedL2
  refine hy.mono hc.aestronglyMeasurable.restrict ?_
  filter_upwards with r
  have hden : 1 + r ^ 2 ≠ 0 := by positivity
  have hw : 0 ≤ affineJapaneseWeight sigma r := by
    unfold affineJapaneseWeight
    positivity
  have hdec : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  have hweight :
      affineJapaneseWeight sigma r ≤ 1 + r ^ 2 :=
    affineJapaneseWeight_le_one_add_sq sigma r hsigma
  have hratio0 :
      0 ≤ affineJapaneseWeight sigma r * (1 + r ^ 2)⁻¹ :=
    mul_nonneg hw hdec
  have hratio1 :
      affineJapaneseWeight sigma r * (1 + r ^ 2)⁻¹ ≤ 1 := by
    calc
      affineJapaneseWeight sigma r * (1 + r ^ 2)⁻¹ ≤
          (1 + r ^ 2) * (1 + r ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hweight hdec
      _ = 1 := by field_simp [hden]
  have hpoint :
      weightedHartreePointwise f r =
        (1 + r ^ 2) * nonlocalApply model r :=
    weightedHartreeAffine_physical_identity r
  have heq :
      affineJapaneseWeight sigma r * nonlocalApply model r =
        (affineJapaneseWeight sigma r * (1 + r ^ 2)⁻¹) *
          weightedHartreePointwise f r := by
    rw [hpoint]
    field_simp [hden]
  calc
    ‖affineJapaneseWeight sigma r * nonlocalApply model r‖ =
        (affineJapaneseWeight sigma r * (1 + r ^ 2)⁻¹) *
          ‖weightedHartreePointwise f r‖ := by
      rw [heq, norm_mul, Real.norm_eq_abs, abs_of_nonneg hratio0]
    _ ≤ 1 * ‖weightedHartreePointwise f r‖ :=
      mul_le_mul_of_nonneg_right hratio1 (norm_nonneg _)
    _ = ‖weightedHartreePointwise f r‖ := one_mul _

#print axioms affineConjugatedModel_memLp_two
#print axioms weightedHartreeAffine_physical_identity
#print axioms nonlocalAffine_continuous
#print axioms nonlocalAffine_inWeightedL2

end HBL.Modulation.Monopole
