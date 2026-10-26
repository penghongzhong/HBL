import HBL.PhaseEnergyInverse
import HBL.WeightedVolterraAPlusMorse

/-!
One complete real-channel Fredholm environment for the actual operator
Aplus = I - V* P V on half-line L2. The negative mode is RETAINED;
only the genuine zero mode is removed. The quantitative inverse estimate
is obtained by separating that negative coefficient and the positive tail,
not by asserting that Aplus is positive on the kernel complement.

This environment supplies the real-channel energy inversion needed by
profile correction and constrained energy analysis. It does not supply an
inverse of the unbounded Hamilton generator or identify the physical
Sobolev completion. No older accepted source is modified.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

abbrev RealEnergyComplement := weightedVolterraAPlus.kerᗮ

private theorem real_mem_complement_iff (x : RealL2 halfLineMeasure) :
    x ∈ RealEnergyComplement ↔ inner ℝ (weightedVolterraSineMode 1) x = 0 := by
  change x ∈ weightedVolterraAPlus.kerᗮ ↔ _
  rw [weightedVolterraAPlus_kernel_eq_sine_span]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

private def realCompactPart :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  ContinuousLinearMap.adjoint weightedVolterraOperator ∘L
    (weightedPotentialOperator ∘L weightedVolterraOperator)

private theorem realCompactPart_compact : IsCompactOperator realCompactPart := by
  exact (weightedVolterraOperator_compact.clm_comp weightedPotentialOperator).clm_comp
    (ContinuousLinearMap.adjoint weightedVolterraOperator)

private theorem real_range : weightedVolterraAPlus.range = RealEnergyComplement := by
  have h := HBL.Fredholm.one_sub_range_eq_adjointKernel_orthogonal
    (K := realCompactPart) realCompactPart_compact
  change weightedVolterraAPlus.range =
    (ContinuousLinearMap.adjoint weightedVolterraAPlus).kerᗮ at h
  have hadj : ContinuousLinearMap.adjoint weightedVolterraAPlus =
      weightedVolterraAPlus := weightedVolterraAPlus_selfAdjoint
  rw [hadj] at h
  exact h

private theorem real_negative_coefficient (x : RealL2 halfLineMeasure) :
    inner ℝ (weightedVolterraSineMode 0) (weightedVolterraAPlus x) =
      (-6 : ℝ) * inner ℝ (weightedVolterraSineMode 0) x := by
  have hsym : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedVolterraAPlus u) v =
        inner ℝ u (weightedVolterraAPlus v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedVolterraAPlus_selfAdjoint
  rw [← hsym, weightedVolterraAPlus_negative_sineMode, real_inner_smul_left]

private theorem real_norm_bound (x : RealL2 halfLineMeasure)
    (hx : x ∈ RealEnergyComplement) :
    ‖x‖ ≤ (58 / 33 : ℝ) * ‖weightedVolterraAPlus x‖ := by
  let n := weightedVolterraSineMode 0
  let c : ℝ := inner ℝ n x
  let r : RealL2 halfLineMeasure := x - c • n
  have hnorm : ‖n‖ = 1 := weightedVolterraSineMode_orthonormal.norm_eq_one 0
  have h00 : inner ℝ n n = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm]
    norm_num
  have h10 : inner ℝ (weightedVolterraSineMode 1) n = 0 :=
    weightedVolterraSineMode_orthonormal.inner_eq_zero (by decide)
  have hrfirst : inner ℝ (weightedVolterraSineMode 0) r = 0 := by
    change inner ℝ n (x - c • n) = 0
    rw [inner_sub_right, real_inner_smul_right, h00]
    dsimp only [c]
    ring
  have hrsecond : inner ℝ (weightedVolterraSineMode 1) r = 0 := by
    change inner ℝ (weightedVolterraSineMode 1) (x - c • n) = 0
    rw [inner_sub_right, real_inner_smul_right,
      (real_mem_complement_iff x).mp hx, h10]
    ring
  have hc : |c| ≤ (1 / 6 : ℝ) * ‖weightedVolterraAPlus x‖ := by
    have hcs := abs_real_inner_le_norm n (weightedVolterraAPlus x)
    rw [hnorm, one_mul] at hcs
    have he : inner ℝ n (weightedVolterraAPlus x) = (-6 : ℝ) * c :=
      real_negative_coefficient x
    rw [he, abs_mul] at hcs
    norm_num at hcs
    linarith
  have hAn : weightedVolterraAPlus n = (-6 : ℝ) • n :=
    weightedVolterraAPlus_negative_sineMode
  have hform : inner ℝ (weightedVolterraAPlus r) r =
      inner ℝ (weightedVolterraAPlus x) r := by
    change inner ℝ (weightedVolterraAPlus (x - c • n)) r = _
    rw [map_sub, map_smul, hAn, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left]
    have hz : inner ℝ n r = 0 := hrfirst
    rw [hz]
    ring
  have hgap := weightedVolterraAPlus_tail_coercive r hrfirst hrsecond
  rw [hform] at hgap
  have hrbound : ‖r‖ ≤ (35 / 22 : ℝ) * ‖weightedVolterraAPlus x‖ := by
    by_cases hr : r = 0
    · rw [hr, norm_zero]
      positivity
    · have hrpos : 0 < ‖r‖ := norm_pos_iff.mpr hr
      have hcs := real_inner_le_norm (weightedVolterraAPlus x) r
      nlinarith
  have hsplit : x = c • n + r := by
    dsimp only [r]
    abel
  calc
    ‖x‖ = ‖c • n + r‖ := congrArg norm hsplit
    _ ≤ ‖c • n‖ + ‖r‖ := norm_add_le _ _
    _ = |c| + ‖r‖ := by rw [norm_smul, hnorm, Real.norm_eq_abs, mul_one]
    _ ≤ (1 / 6 : ℝ) * ‖weightedVolterraAPlus x‖ +
        (35 / 22 : ℝ) * ‖weightedVolterraAPlus x‖ := add_le_add hc hrbound
    _ = (58 / 33 : ℝ) * ‖weightedVolterraAPlus x‖ := by ring

private theorem real_preserves (x : RealL2 halfLineMeasure)
    (_hx : x ∈ RealEnergyComplement) :
    weightedVolterraAPlus x ∈ RealEnergyComplement := by
  rw [real_mem_complement_iff]
  have hsym : ∀ u v : RealL2 halfLineMeasure,
      inner ℝ (weightedVolterraAPlus u) v =
        inner ℝ u (weightedVolterraAPlus v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      weightedVolterraAPlus_selfAdjoint
  rw [← hsym, weightedVolterraAPlus_zero_sineMode, inner_zero_left]

def realEnergyRestriction : RealEnergyComplement →L[ℝ] RealEnergyComplement :=
  weightedVolterraAPlus.restrict real_preserves

private theorem realRestriction_bijective : Function.Bijective realEnergyRestriction := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hz : weightedVolterraAPlus ((x : RealL2 halfLineMeasure) - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hb := real_norm_bound ((x : RealL2 halfLineMeasure) - y)
      (RealEnergyComplement.sub_mem x.property y.property)
    rw [hz, norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  · intro f
    have hf : (f : RealL2 halfLineMeasure) ∈ weightedVolterraAPlus.range := by
      rw [real_range]
      exact f.property
    obtain ⟨x, hx⟩ := hf
    let y := weightedVolterraAPlus.kerᗮ.orthogonalProjectionOnto x
    have hy : weightedVolterraAPlus (y : RealL2 halfLineMeasure) = f := by
      change weightedVolterraAPlus
        (weightedVolterraAPlus.kerᗮ.starProjection x) = f
      rw [weightedVolterraAPlus.ker.starProjection_orthogonal_val, map_sub]
      have hz : weightedVolterraAPlus
          (weightedVolterraAPlus.ker.starProjection x) = 0 :=
        (weightedVolterraAPlus.ker.orthogonalProjectionOnto x).property
      rw [hz, sub_zero]
      exact hx
    exact ⟨y, Subtype.ext hy⟩

private def realEnergyEquiv : RealEnergyComplement ≃L[ℝ] RealEnergyComplement :=
  ContinuousLinearEquiv.ofBijective realEnergyRestriction
    (LinearMap.ker_eq_bot.mpr realRestriction_bijective.1)
    (LinearMap.range_eq_top.mpr realRestriction_bijective.2)

def realEnergyInverse : RealEnergyComplement →L[ℝ] RealEnergyComplement :=
  realEnergyEquiv.symm.toContinuousLinearMap

private theorem realInverse_right (f : RealEnergyComplement) :
    realEnergyRestriction (realEnergyInverse f) = f :=
  realEnergyEquiv.apply_symm_apply f

private theorem realInverse_left (x : RealEnergyComplement) :
    realEnergyInverse (realEnergyRestriction x) = x :=
  realEnergyEquiv.symm_apply_apply x

private theorem realInverse_norm : ‖realEnergyInverse‖ ≤ (58 / 33 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hb := real_norm_bound (realEnergyInverse f : RealL2 halfLineMeasure)
    (realEnergyInverse f).property
  have heq := congrArg Subtype.val (realInverse_right f)
  change weightedVolterraAPlus
    (realEnergyInverse f : RealL2 halfLineMeasure) = (f : RealL2 halfLineMeasure) at heq
  rw [heq] at hb
  exact hb

/-- R9: exact compatibility, genuine two-sided bounded inverse, uniqueness,
retained negative coefficient, Lipschitz control and C1 source dependence.
The conclusions are derived for the actual operator; none of them are
assumptions. The explicit constant is convenient, not asserted optimal. -/
theorem realEnergyInverse_certified :
    weightedVolterraAPlus.range = RealEnergyComplement ∧
    (∀ f : RealL2 halfLineMeasure,
      (∃ x : RealL2 halfLineMeasure, weightedVolterraAPlus x = f) ↔
        inner ℝ (weightedVolterraSineMode 1) f = 0) ∧
    (∀ f : RealEnergyComplement,
      realEnergyRestriction (realEnergyInverse f) = f) ∧
    (∀ x : RealEnergyComplement,
      realEnergyInverse (realEnergyRestriction x) = x) ∧
    ‖realEnergyInverse‖ ≤ (58 / 33 : ℝ) ∧
    (∀ f : RealEnergyComplement,
      ∃! x : RealEnergyComplement, realEnergyRestriction x = f) ∧
    (∀ f : RealEnergyComplement,
      inner ℝ (weightedVolterraSineMode 0)
        (realEnergyInverse f : RealL2 halfLineMeasure) =
        -(1 / 6 : ℝ) * inner ℝ (weightedVolterraSineMode 0)
          (f : RealL2 halfLineMeasure)) ∧
    (∀ f g : RealEnergyComplement,
      ‖realEnergyInverse f - realEnergyInverse g‖ ≤ (58 / 33 : ℝ) * ‖f - g‖) ∧
    (∀ F : ℝ → RealEnergyComplement,
      ContDiff ℝ 1 F → ContDiff ℝ 1 (fun s => realEnergyInverse (F s))) := by
  refine ⟨real_range, ?_, realInverse_right, realInverse_left, realInverse_norm, ?_, ?_, ?_, ?_⟩
  · intro f
    change f ∈ weightedVolterraAPlus.range ↔ _
    rw [real_range, real_mem_complement_iff]
  · intro f
    refine ⟨realEnergyInverse f, realInverse_right f, ?_⟩
    intro x hx
    exact realRestriction_bijective.1 (hx.trans (realInverse_right f).symm)
  · intro f
    have heq := congrArg Subtype.val (realInverse_right f)
    change weightedVolterraAPlus
      (realEnergyInverse f : RealL2 halfLineMeasure) = (f : RealL2 halfLineMeasure) at heq
    have hc := real_negative_coefficient (realEnergyInverse f : RealL2 halfLineMeasure)
    rw [heq] at hc
    linarith
  · intro f g
    rw [← map_sub]
    exact (realEnergyInverse.le_opNorm (f - g)).trans
      (mul_le_mul_of_nonneg_right realInverse_norm (norm_nonneg _))
  · intro F hF
    exact realEnergyInverse.contDiff.comp hF

end HBL.Modulation.Monopole
