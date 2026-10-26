import HBL.PhysicalVectorGradient
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
R17: identify the actual physical phase Hessian on EVERY constructed energy
state, not only on the compact core. The weight W^2 is proved to lie in L3(R3),
so multiplication maps actual L6 functions to L2. The kinetic and potential
pairings are absolutely integrable and jointly continuous. Core agreement,
completion and real polarization identify the full bilinear integral with
4*pi times the SAME Aminus energy operator. Nonnegativity and the original
compact-test coercivity follow without a new form-identity hypothesis.
This is the local phase channel, NOT the nonlocal real channel or a Hamilton
propagator. No converse Sobolev density or new axiom is introduced.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

local instance : Fact ((1 : ENNReal) ≤ 3) := ⟨by norm_num⟩
local instance : Fact ((1 : ENNReal) ≤ 6) := ⟨by norm_num⟩
local instance : ENNReal.HolderTriple 3 6 2 where
  inv_add_inv_eq_inv := by
    change ((3 : ℝ≥0) : ENNReal)⁻¹ + ((6 : ℝ≥0) : ENNReal)⁻¹ =
      ((2 : ℝ≥0) : ENNReal)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (3 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
    norm_num

/-- The actual square of the physical bubble. -/
def physicalPhaseWeight (x : PhysicalRadialSpace3) : ℝ := bubble ‖x‖ ^ 2

private theorem weightMem :
    MemLp physicalPhaseWeight 3 (volume : Measure PhysicalRadialSpace3) := by
  have hm : AEStronglyMeasurable physicalPhaseWeight
      (volume : Measure PhysicalRadialSpace3) :=
    ((bubble_contDiff.continuous.comp continuous_norm).pow 2).aestronglyMeasurable
  have hi : Integrable (fun x : PhysicalRadialSpace3 =>
      (1 + ‖x‖ ^ 2) ^ (-(6 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num [PhysicalRadialSpace3])
  apply (integrable_norm_rpow_iff hm
    (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num : (3 : ENNReal) ≠ ⊤)).mp
  apply hi.congr
  filter_upwards with x
  change (1 + ‖x‖ ^ 2) ^ (-(6 : ℝ) / 2) =
    ‖physicalPhaseWeight x‖ ^ (3 : ENNReal).toReal
  change (1 + ‖x‖ ^ 2) ^ (-(6 : ℝ) / 2) =
    |bubble ‖x‖ ^ 2| ^ (3 : ℝ)
  rw [show -(6 : ℝ) / 2 = -3 by norm_num,
    abs_of_nonneg (sq_nonneg (bubble ‖x‖)), bubble_sq,
    Real.rpow_neg (by positivity)]
  exact (Real.inv_rpow (by positivity : 0 ≤ 1 + ‖x‖ ^ 2) (3 : ℝ)).symm

abbrev PhysicalScalarL2 := Lp ℝ 2 (volume : Measure PhysicalRadialSpace3)

/-- Multiplication by the genuine physical W^2, constructed by Holder. -/
def physicalPhaseMultiplier : PhysicalL6 →L[ℝ] PhysicalScalarL2 :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (volume : Measure PhysicalRadialSpace3)
    3 6 2 (weightMem.toLp physicalPhaseWeight)

/-- The same R14 L6 realization, multiplied by the physical weight. -/
def physicalWeightedState : PhysicalRadialEnergyCompletion →L[ℝ] PhysicalScalarL2 :=
  physicalPhaseMultiplier.comp physicalL6Realization

private theorem weighted_ae (u : PhysicalRadialEnergyCompletion) :
    (physicalWeightedState u : PhysicalRadialSpace3 → ℝ) =ᵐ[volume]
      (fun x => physicalPhaseWeight x * physicalL6Realization u x) := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := (2 : ENNReal)) (weightMem.toLp physicalPhaseWeight) (physicalL6Realization u)
  filter_upwards [h, weightMem.coeFn_toLp] with x hx hw
  change physicalWeightedState u x =
    (weightMem.toLp physicalPhaseWeight : PhysicalRadialSpace3 → ℝ) x *
      physicalL6Realization u x at hx
  rw [hx, hw]

private theorem potential_integrable (u v : PhysicalRadialEnergyCompletion) :
    Integrable (fun x : PhysicalRadialSpace3 =>
      bubble ‖x‖ ^ 4 * physicalL6Realization u x * physicalL6Realization v x) := by
  have hi := memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1
      (Lp.memLp (physicalWeightedState u)) (Lp.memLp (physicalWeightedState v)))
  apply hi.congr
  filter_upwards [weighted_ae u, weighted_ae v] with x hu hv
  change physicalWeightedState u x * physicalWeightedState v x = _
  rw [hu, hv]
  unfold physicalPhaseWeight
  ring

private theorem potential_pair (u v : PhysicalRadialEnergyCompletion) :
    inner ℝ (physicalWeightedState u) (physicalWeightedState v) =
      ∫ x : PhysicalRadialSpace3,
        bubble ‖x‖ ^ 4 * physicalL6Realization u x * physicalL6Realization v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weighted_ae u, weighted_ae v] with x hu hv
  rw [hu, hv, Real.inner_apply]
  unfold physicalPhaseWeight
  ring

private theorem kinetic_integrable (u v : PhysicalRadialEnergyCompletion) :
    Integrable (fun x : PhysicalRadialSpace3 =>
      inner ℝ (physicalGradientRealization u x) (physicalGradientRealization v x)) := by
  have hi := memLp_one_iff_integrable.mp
    ((innerSL ℝ : PhysicalRadialSpace3 →L[ℝ] PhysicalRadialSpace3 →L[ℝ] ℝ).memLp_of_bilin 1
      (Lp.memLp (physicalGradientRealization u)) (Lp.memLp (physicalGradientRealization v)))
  exact hi

/-- The actual three-dimensional phase Hessian bilinear integral. -/
def physicalPhaseHessian (u v : PhysicalRadialEnergyCompletion) : ℝ :=
  (∫ x : PhysicalRadialSpace3,
    inner ℝ (physicalGradientRealization u x) (physicalGradientRealization v x)) -
  3 * (∫ x : PhysicalRadialSpace3,
    bubble ‖x‖ ^ 4 * physicalL6Realization u x * physicalL6Realization v x)

private theorem hessian_pair (u v : PhysicalRadialEnergyCompletion) :
    physicalPhaseHessian u v =
      inner ℝ (physicalGradientRealization u) (physicalGradientRealization v) -
      3 * inner ℝ (physicalWeightedState u) (physicalWeightedState v) := by
  rw [potential_pair, L2.inner_def]
  rfl

private theorem hessian_diagonal (u : PhysicalRadialEnergyCompletion) :
    ‖physicalGradientRealization u‖ ^ 2 - 3 * ‖physicalWeightedState u‖ ^ 2 =
      completedPhysicalPhaseForm u := by
  have hcont : Continuous (fun u : PhysicalRadialEnergyCompletion =>
      ‖physicalGradientRealization u‖ ^ 2 - 3 * ‖physicalWeightedState u‖ ^ 2) :=
    (physicalGradientRealization.continuous.norm.pow 2).sub
      (continuous_const.mul (physicalWeightedState.continuous.norm.pow 2))
  have hcore (f : PhysicalGradientCore) :
      ‖physicalGradientRealization (f : PhysicalRadialEnergyCompletion)‖ ^ 2 -
        3 * ‖physicalWeightedState (f : PhysicalRadialEnergyCompletion)‖ ^ 2 =
      physicalRadial3PhaseQuadratic f := by
    have hp : ‖physicalWeightedState (f : PhysicalRadialEnergyCompletion)‖ ^ 2 =
        ∫ x : PhysicalRadialSpace3, bubble ‖x‖ ^ 4 * f ‖x‖ * f ‖x‖ := by
      rw [← real_inner_self_eq_norm_sq, potential_pair]
      apply integral_congr_ae
      filter_upwards [physicalL6Realization_certified.2.1 f] with x hx
      rw [hx]
      rfl
    rw [physicalVectorGradient_certified.2.2.1,
      UniformSpace.Completion.norm_coe, hp]
    unfold physicalRadial3PhaseQuadratic
    rw [physicalEnergyCompletion_certified.2.1 f]
  have he := physicalEnergyCompletion_certified.2.2.2.2.2.2.2.1
    (fun u => ‖physicalGradientRealization u‖ ^ 2 - 3 * ‖physicalWeightedState u‖ ^ 2)
    hcont hcore
  exact congrFun he u

private theorem hessian_coordinate (u v : PhysicalRadialEnergyCompletion) :
    physicalPhaseHessian u v = (4 * Real.pi) *
      inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding u)) (physicalEnergyEmbedding v) := by
  rw [hessian_pair]
  have hu := hessian_diagonal u
  have hv := hessian_diagonal v
  have hs := hessian_diagonal (u + v)
  unfold completedPhysicalPhaseForm at hu hv hs
  simp only [map_add, norm_add_sq_real, inner_add_left, inner_add_right] at hs
  have hsym : inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding v))
        (physicalEnergyEmbedding u) =
      inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding u)) (physicalEnergyEmbedding v) := by
    have he : inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding v))
        (physicalEnergyEmbedding u) =
        inner ℝ (physicalEnergyEmbedding v) (weightedVolterraAMinus (physicalEnergyEmbedding u)) :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        weightedVolterraAMinus_selfAdjoint) (physicalEnergyEmbedding v) (physicalEnergyEmbedding u)
    exact he.trans (real_inner_comm _ _)
  rw [hsym] at hs
  nlinarith only [hu, hv, hs]

private theorem hessian_continuous :
    Continuous (fun p : PhysicalRadialEnergyCompletion × PhysicalRadialEnergyCompletion =>
      physicalPhaseHessian p.1 p.2) := by
  simp_rw [hessian_pair]
  exact ((physicalGradientRealization.continuous.comp continuous_fst).inner
    (physicalGradientRealization.continuous.comp continuous_snd)).sub
    (continuous_const.mul
      ((physicalWeightedState.continuous.comp continuous_fst).inner
        (physicalWeightedState.continuous.comp continuous_snd)))

private theorem hessian_bound (u v : PhysicalRadialEnergyCompletion) :
    |physicalPhaseHessian u v| ≤
      (4 * Real.pi) * ‖weightedVolterraAMinus‖ * ‖u‖ * ‖v‖ := by
  rw [hessian_coordinate, abs_mul, abs_of_nonneg (show 0 ≤ 4 * Real.pi by positivity)]
  have hi : |inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding u))
      (physicalEnergyEmbedding v)| ≤
      ‖weightedVolterraAMinus (physicalEnergyEmbedding u)‖ * ‖physicalEnergyEmbedding v‖ :=
    by simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (weightedVolterraAMinus (physicalEnergyEmbedding u))
        (physicalEnergyEmbedding v))
  have ho := weightedVolterraAMinus.le_opNorm (physicalEnergyEmbedding u)
  have hb := hi.trans (mul_le_mul_of_nonneg_right ho (norm_nonneg _))
  have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * Real.pi by positivity)
  rw [physicalEnergyCompletion_certified.2.2.2.1,
    physicalEnergyCompletion_certified.2.2.2.1] at h
  nlinarith only [h]

/-- One complete R17 environment: actual integrable physical phase Hessian,
its full energy-coordinate identity and compact-gauge physical coercivity. -/
theorem physicalPhaseHessian_certified :
    MemLp physicalPhaseWeight 3 (volume : Measure PhysicalRadialSpace3) ∧
    (∀ u v : PhysicalRadialEnergyCompletion,
      Integrable (fun x : PhysicalRadialSpace3 =>
        inner ℝ (physicalGradientRealization u x) (physicalGradientRealization v x)) ∧
      Integrable (fun x : PhysicalRadialSpace3 =>
        bubble ‖x‖ ^ 4 * physicalL6Realization u x * physicalL6Realization v x)) ∧
    (∀ u v : PhysicalRadialEnergyCompletion, physicalPhaseHessian u v =
      (4 * Real.pi) * inner ℝ (weightedVolterraAMinus (physicalEnergyEmbedding u))
        (physicalEnergyEmbedding v)) ∧
    Continuous (fun p : PhysicalRadialEnergyCompletion × PhysicalRadialEnergyCompletion =>
      physicalPhaseHessian p.1 p.2) ∧
    (∀ u v : PhysicalRadialEnergyCompletion, |physicalPhaseHessian u v| ≤
      (4 * Real.pi) * ‖weightedVolterraAMinus‖ * ‖u‖ * ‖v‖) ∧
    (∀ u : PhysicalRadialEnergyCompletion, 0 ≤ physicalPhaseHessian u u) ∧
    0 < phaseCompactGap ∧
    (∀ u : PhysicalRadialEnergyCompletion, completedPhaseTest u = 0 →
      phaseCompactGap * ‖physicalGradientRealization u‖ ^ 2 ≤ physicalPhaseHessian u u) := by
  refine ⟨weightMem, (fun u v => ⟨kinetic_integrable u v, potential_integrable u v⟩),
    hessian_coordinate, hessian_continuous, hessian_bound, ?_,
    actualCompactPhaseSlice_certified.2.1, ?_⟩
  · intro u
    rw [hessian_coordinate]
    exact mul_nonneg (by positivity)
      (weightedVolterraAMinus_nonneg (physicalEnergyEmbedding u))
  · intro u hu
    have h := actualCompactPhaseSlice_certified.2.2.2.1 (physicalEnergyEmbedding u) hu
    have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * Real.pi by positivity)
    rw [physicalEnergyCompletion_certified.2.2.2.1] at hm
    rw [hessian_coordinate, physicalVectorGradient_certified.2.2.1]
    nlinarith only [hm]

end HBL.Modulation.Monopole
