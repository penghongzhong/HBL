import HBL.PhaseBubbleKernel
import HBL.FredholmCokernelAlternative
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
A concrete normalized inverse for the already constructed phase operator.
This is the Riesz energy realization Aminus = I - 3 V*V on actual half-line
L2, with the physical bubble derivative q_W as its precise kernel.

No inverse, range identity, or solvability estimate is assumed. Compactness,
self-adjointness, the exact bubble kernel and the proved 4/5 gap give the
inverse. Its C1 action concerns actual source paths in the complement.

This does NOT turn the energy inverse into an inverse of the unbounded
Hamiltonian generator or a zero-centre Sylvester map. Those domain and
source-space identifications in manuscript Proposition 3.2 remain open.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The actual Hilbert energy space with the physical phase kernel removed. -/
abbrev PhaseEnergyComplement := weightedVolterraAMinus.kerᗮ

private theorem phase_mem_complement_iff (x : RealL2 halfLineMeasure) :
    x ∈ PhaseEnergyComplement ↔ inner ℝ fullBubbleRadialEnergyL2 x = 0 := by
  change x ∈ weightedVolterraAMinus.kerᗮ ↔ _
  rw [weightedVolterraAMinus_kernel_eq_bubble_span]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

private theorem phase_adjoint_eq :
    ContinuousLinearMap.adjoint weightedVolterraAMinus = weightedVolterraAMinus := by
  exact weightedVolterraAMinus_selfAdjoint

private def phaseCompactPart :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  (3 : ℝ) • (ContinuousLinearMap.adjoint weightedVolterraOperator ∘L
    weightedVolterraOperator)

private theorem phaseCompactPart_compact : IsCompactOperator phaseCompactPart := by
  exact (weightedVolterraOperator_compact.clm_comp
    (ContinuousLinearMap.adjoint weightedVolterraOperator)).smul (3 : ℝ)

private theorem phase_range : weightedVolterraAMinus.range = PhaseEnergyComplement := by
  have h := HBL.Fredholm.one_sub_range_eq_adjointKernel_orthogonal
    (K := phaseCompactPart) phaseCompactPart_compact
  change weightedVolterraAMinus.range =
    (ContinuousLinearMap.adjoint weightedVolterraAMinus).kerᗮ at h
  rw [phase_adjoint_eq] at h
  exact h

private theorem phase_norm_bound (x : RealL2 halfLineMeasure)
    (hx : x ∈ PhaseEnergyComplement) :
    ‖x‖ ≤ (5 / 4 : ℝ) * ‖weightedVolterraAMinus x‖ := by
  have hphase := (phaseBubble_orthogonal_iff x).mp
    ((phase_mem_complement_iff x).mp hx)
  have hgap := weightedVolterraAMinus_tail_coercive x hphase
  have hcs := real_inner_le_norm (weightedVolterraAMinus x) x
  by_cases hz : x = 0
  · simp [hz]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hz
    nlinarith

private theorem phase_preserves (x : RealL2 halfLineMeasure)
    (_hx : x ∈ PhaseEnergyComplement) :
    weightedVolterraAMinus x ∈ PhaseEnergyComplement := by
  rw [phase_mem_complement_iff]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    weightedVolterraAMinus_selfAdjoint
  calc
    inner ℝ fullBubbleRadialEnergyL2 (weightedVolterraAMinus x) =
        inner ℝ (weightedVolterraAMinus fullBubbleRadialEnergyL2) x :=
      (hsym fullBubbleRadialEnergyL2 x).symm
    _ = 0 := by rw [weightedVolterraAMinus_bubble_zero, inner_zero_left]

/-- Restriction of the genuine phase operator, not a newly postulated map. -/
def phaseEnergyRestriction : PhaseEnergyComplement →L[ℝ] PhaseEnergyComplement :=
  weightedVolterraAMinus.restrict phase_preserves

private theorem phaseRestriction_bijective : Function.Bijective phaseEnergyRestriction := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hzero : weightedVolterraAMinus ((x : RealL2 halfLineMeasure) - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hbound := phase_norm_bound ((x : RealL2 halfLineMeasure) - y)
      (PhaseEnergyComplement.sub_mem x.property y.property)
    rw [hzero, norm_zero, mul_zero] at hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))
  · intro f
    have hf : (f : RealL2 halfLineMeasure) ∈ weightedVolterraAMinus.range := by
      rw [phase_range]
      exact f.property
    obtain ⟨x, hx⟩ := hf
    let y := weightedVolterraAMinus.kerᗮ.orthogonalProjectionOnto x
    have hy : weightedVolterraAMinus (y : RealL2 halfLineMeasure) = f := by
      change weightedVolterraAMinus
        (weightedVolterraAMinus.kerᗮ.starProjection x) = f
      rw [weightedVolterraAMinus.ker.starProjection_orthogonal_val, map_sub]
      have hz : weightedVolterraAMinus
          (weightedVolterraAMinus.ker.starProjection x) = 0 :=
        (weightedVolterraAMinus.ker.orthogonalProjectionOnto x).property
      rw [hz, sub_zero]
      exact hx
    exact ⟨y, Subtype.ext hy⟩

private def phaseEnergyEquiv : PhaseEnergyComplement ≃L[ℝ] PhaseEnergyComplement :=
  ContinuousLinearEquiv.ofBijective phaseEnergyRestriction
    (LinearMap.ker_eq_bot.mpr phaseRestriction_bijective.1)
    (LinearMap.range_eq_top.mpr phaseRestriction_bijective.2)

/-- The actual normalized bounded inverse of the phase-energy operator. -/
def phaseEnergyInverse : PhaseEnergyComplement →L[ℝ] PhaseEnergyComplement :=
  phaseEnergyEquiv.symm.toContinuousLinearMap

private theorem phaseInverse_right (f : PhaseEnergyComplement) :
    phaseEnergyRestriction (phaseEnergyInverse f) = f :=
  phaseEnergyEquiv.apply_symm_apply f

private theorem phaseInverse_left (x : PhaseEnergyComplement) :
    phaseEnergyInverse (phaseEnergyRestriction x) = x :=
  phaseEnergyEquiv.symm_apply_apply x

private theorem phaseInverse_norm : ‖phaseEnergyInverse‖ ≤ (5 / 4 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hb := phase_norm_bound (phaseEnergyInverse f : RealL2 halfLineMeasure)
    (phaseEnergyInverse f).property
  have heq := congrArg Subtype.val (phaseInverse_right f)
  change weightedVolterraAMinus
    (phaseEnergyInverse f : RealL2 halfLineMeasure) = (f : RealL2 halfLineMeasure) at heq
  rw [heq] at hb
  exact hb

/-- Complete concrete phase Fredholm theorem: exact compatibility with
q_W, a genuine inverse on q_W-perp with norm at most 5/4, two-sided inverse
identities, uniqueness of normalized solutions, and C1 source-path transfer.
This is one terminal analytic theorem; it is not manuscript Lemma 3.3. -/
theorem phaseEnergyInverse_certified :
    (∀ f : RealL2 halfLineMeasure,
      (∃ x : RealL2 halfLineMeasure, weightedVolterraAMinus x = f) ↔
        inner ℝ fullBubbleRadialEnergyL2 f = 0) ∧
    (∀ f : PhaseEnergyComplement,
      phaseEnergyRestriction (phaseEnergyInverse f) = f) ∧
    (∀ x : PhaseEnergyComplement,
      phaseEnergyInverse (phaseEnergyRestriction x) = x) ∧
    ‖phaseEnergyInverse‖ ≤ (5 / 4 : ℝ) ∧
    (∀ f : PhaseEnergyComplement,
      ∃! x : PhaseEnergyComplement, phaseEnergyRestriction x = f) ∧
    (∀ F : ℝ → PhaseEnergyComplement,
      ContDiff ℝ 1 F → ContDiff ℝ 1 (fun s => phaseEnergyInverse (F s))) := by
  refine ⟨?_, phaseInverse_right, phaseInverse_left, phaseInverse_norm, ?_, ?_⟩
  · intro f
    change f ∈ weightedVolterraAMinus.range ↔ _
    rw [phase_range, phase_mem_complement_iff]
  · intro f
    refine ⟨phaseEnergyInverse f, phaseInverse_right f, ?_⟩
    intro x hx
    exact phaseRestriction_bijective.1 (hx.trans (phaseInverse_right f).symm)
  · intro F hF
    exact phaseEnergyInverse.contDiff.comp hF

end HBL.Modulation.Monopole
