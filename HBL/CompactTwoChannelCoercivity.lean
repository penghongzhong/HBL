import HBL.PhysicalScaleNormalization
import HBL.CompactPhaseNormalization

/-!
R11: coercivity of the actual two-channel energy form on the original
compact scale and phase slices, after one physical negative-direction
constraint. All operators, tests, and zero modes are the existing concrete
ones. The original Hartree radial integral form is retained on the smooth
finite-energy core; no global L2 condition on r*f is imposed.

This is static energy coercivity. It does not construct a Hamilton flow,
identify Hamilton hyperbolic constraints, or assert the completed physical
three-dimensional nonlocal Hessian identity.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Loss for the original compact scale gauge, not an orthogonal gauge. -/
def scaleCompactGap : ℝ := (22 / 35 : ℝ) / scaleCompactLoss ^ 2

/-- One positive constant controlling both actual channel forms. -/
def compactTwoChannelGap : ℝ := min scaleCompactGap phaseCompactGap

private theorem scale_gap_pos : 0 < scaleCompactGap := by
  unfold scaleCompactGap scaleCompactLoss
  positivity

private theorem joint_gap_pos : 0 < compactTwoChannelGap := by
  exact lt_min scale_gap_pos actualCompactPhaseSlice_certified.2.1

private theorem scale_test_one : scaleCompactTest weightedVolterraScaleVector = 1 :=
  physicalScaleNormalization_certified.2.2.2.2.2.1

private theorem scale_zero : weightedVolterraAPlus weightedVolterraScaleVector = 0 :=
  physicalScaleNormalization_certified.2.2.2.1

private theorem scale_first_orthogonal :
    inner ℝ (weightedVolterraSineMode 0) weightedVolterraScaleVector = 0 := by
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    weightedVolterraAPlus_selfAdjoint)
    (weightedVolterraSineMode 0) weightedVolterraScaleVector
  rw [weightedVolterraAPlus_negative_sineMode, scale_zero,
    real_inner_smul_left, inner_zero_right] at hs
  linarith

private theorem scale_projection_bound (q : FullRadialEnergyL2) :
    ‖scaleCompactProjection q‖ ≤ scaleCompactLoss * ‖q‖ := by
  change ‖q - scaleCompactTest q • weightedVolterraScaleVector‖ ≤ _
  calc
    ‖q - scaleCompactTest q • weightedVolterraScaleVector‖ ≤
        ‖q‖ + ‖scaleCompactTest q • weightedVolterraScaleVector‖ := norm_sub_le _ _
    _ = ‖q‖ + ‖scaleCompactTest q‖ * ‖weightedVolterraScaleVector‖ := by
      rw [norm_smul]
    _ ≤ ‖q‖ + (‖scaleCompactTest‖ * ‖q‖) * ‖weightedVolterraScaleVector‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (scaleCompactTest.le_opNorm q)
        (norm_nonneg _))
    _ = scaleCompactLoss * ‖q‖ := by unfold scaleCompactLoss; ring

private theorem real_compact_gap (q : FullRadialEnergyL2)
    (hq : scaleCompactTest q = 0)
    (hnegative : inner ℝ fullBubbleRadialEnergyL2 q = 0) :
    scaleCompactGap * ‖q‖ ^ 2 ≤ inner ℝ (weightedVolterraAPlus q) q := by
  let k := weightedVolterraScaleVector
  let c : ℝ := inner ℝ k q / inner ℝ k k
  let r : FullRadialEnergyL2 := q - c • k
  have hkpos : 0 < inner ℝ k k := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr weightedVolterraScaleVector_ne_zero)
  have hrk : inner ℝ weightedVolterraScaleVector r = 0 := by
    change inner ℝ k (q - c • k) = 0
    rw [inner_sub_right, real_inner_smul_right]
    dsimp only [c]
    rw [div_mul_cancel₀ _ (ne_of_gt hkpos), sub_self]
  have hrsecond : inner ℝ (weightedVolterraSineMode 1) r = 0 := by
    have hm : r ∈ (Submodule.span ℝ {weightedVolterraScaleVector})ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hrk
    rw [← weightedVolterraAPlus_kernel_eq_span,
      weightedVolterraAPlus_kernel_eq_sine_span] at hm
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hm
  have hrfirst : inner ℝ (weightedVolterraSineMode 0) r = 0 := by
    change inner ℝ (weightedVolterraSineMode 0)
      (q - c • weightedVolterraScaleVector) = 0
    rw [inner_sub_right, real_inner_smul_right,
      (phaseBubble_orthogonal_iff q).mp hnegative, scale_first_orthogonal]
    ring
  have hrtest : scaleCompactTest r = -c := by
    change scaleCompactTest (q - c • weightedVolterraScaleVector) = -c
    rw [map_sub, map_smul, hq, scale_test_one]
    simp
  have hqrep : q = scaleCompactProjection r := by
    change q = r - scaleCompactTest r • k
    rw [hrtest, neg_smul, sub_neg_eq_add]
    dsimp only [r]
    abel
  have hAr : weightedVolterraAPlus r = weightedVolterraAPlus q := by
    change weightedVolterraAPlus (q - c • weightedVolterraScaleVector) = _
    rw [map_sub, map_smul, scale_zero, smul_zero, sub_zero]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    weightedVolterraAPlus_selfAdjoint
  have hcross : inner ℝ (weightedVolterraAPlus q) k = 0 := by
    calc
      inner ℝ (weightedVolterraAPlus q) k =
          inner ℝ q (weightedVolterraAPlus k) := hsym q k
      _ = 0 := by
        change inner ℝ q (weightedVolterraAPlus weightedVolterraScaleVector) = 0
        rw [scale_zero, inner_zero_right]
  have hform : inner ℝ (weightedVolterraAPlus r) r =
      inner ℝ (weightedVolterraAPlus q) q := by
    rw [hAr]
    dsimp only [r]
    rw [inner_sub_right, real_inner_smul_right, hcross, mul_zero, sub_zero]
  have hgap := weightedVolterraAPlus_tail_coercive r hrfirst hrsecond
  rw [hform] at hgap
  have hnorm : ‖q‖ ≤ scaleCompactLoss * ‖r‖ := by
    calc
      ‖q‖ = ‖scaleCompactProjection r‖ := congrArg norm hqrep
      _ ≤ scaleCompactLoss * ‖r‖ := scale_projection_bound r
  have hL : 0 < scaleCompactLoss := by unfold scaleCompactLoss; positivity
  have hsquare : ‖q‖ ^ 2 ≤ scaleCompactLoss ^ 2 * ‖r‖ ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg (mul_nonneg hL.le (norm_nonneg r)) (norm_nonneg q))
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hgap (sq_nonneg scaleCompactLoss)
  unfold scaleCompactGap
  rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hL)]
  nlinarith

private theorem joint_compact_gap (q p : FullRadialEnergyL2)
    (hq : scaleCompactTest q = 0) (hp : phaseCompactTest p = 0)
    (hnegative : inner ℝ fullBubbleRadialEnergyL2 q = 0) :
    compactTwoChannelGap * (‖q‖ ^ 2 + ‖p‖ ^ 2) ≤
      inner ℝ (weightedVolterraAPlus q) q +
        inner ℝ (weightedVolterraAMinus p) p := by
  have hreal := real_compact_gap q hq hnegative
  have hphase := actualCompactPhaseSlice_certified.2.2.2.1 p hp
  have hqbound := mul_le_mul_of_nonneg_right
    (min_le_left scaleCompactGap phaseCompactGap) (sq_nonneg ‖q‖)
  have hpbound := mul_le_mul_of_nonneg_right
    (min_le_right scaleCompactGap phaseCompactGap) (sq_nonneg ‖p‖)
  unfold compactTwoChannelGap
  nlinarith only [hreal, hphase, hqbound, hpbound]

/-- The original radial integral expression, not a renamed operator form. -/
def compactTwoChannelProfileForm (f g : ℝ → ℝ) : ℝ :=
  ((∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) -
    (9 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * radialU f r * radialU f r
      ∂halfLineMeasure) +
    ∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 * (radialU f p.1 * radialU f p.2)
      ∂(halfLineMeasure.prod halfLineMeasure))) +
  ((∫ r : ℝ, (deriv (radialU g) r) ^ 2 ∂halfLineMeasure) -
    3 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * radialU g r * radialU g r
      ∂halfLineMeasure))

private theorem actual_profile_form
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfm : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgm : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    compactTwoChannelProfileForm f g =
      inner ℝ (weightedVolterraAPlus (smoothToRadialDotH1 f hfm))
        (smoothToRadialDotH1 f hfm) +
      inner ℝ (weightedVolterraAMinus (smoothToRadialDotH1 g hgm))
        (smoothToRadialDotH1 g hgm) := by
  rw [weightedVolterraAPlus_radial_profile_pairing f f hf hf hfm hfm,
    weightedVolterraAMinus_radial_profile_pairing g g hg hg hgm hgm]
  simp only [compactTwoChannelProfileForm, pow_two]

/-- R11: a complete original-test two-channel coercivity environment.
The single negative constraint is the explicit physical bubble-energy
pairing, not a presumed Hamilton spectral projection. The smooth-core
conclusion retains the actual radial Hartree kernel and does not require
compact support or ordinary L2 membership of the unweighted profiles. -/
theorem actualCompactTwoChannelCoercivity_certified :
    0 < scaleCompactGap ∧ 0 < compactTwoChannelGap ∧
    (∀ q : FullRadialEnergyL2,
      scaleCompactTest q = 0 → inner ℝ fullBubbleRadialEnergyL2 q = 0 →
      scaleCompactGap * ‖q‖ ^ 2 ≤ inner ℝ (weightedVolterraAPlus q) q) ∧
    (∀ q p : FullRadialEnergyL2,
      scaleCompactTest q = 0 → phaseCompactTest p = 0 →
      inner ℝ fullBubbleRadialEnergyL2 q = 0 →
      compactTwoChannelGap * (‖q‖ ^ 2 + ‖p‖ ^ 2) ≤
        inner ℝ (weightedVolterraAPlus q) q +
          inner ℝ (weightedVolterraAMinus p) p) ∧
    (∀ (f g : ℝ → ℝ) (_hf : ContDiff ℝ 1 f) (_hg : ContDiff ℝ 1 g)
      (_hfm : MemLp (deriv (radialU f)) 2 halfLineMeasure)
      (_hgm : MemLp (deriv (radialU g)) 2 halfLineMeasure),
      (∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaPlus r * radialU f r) = 0 →
      (∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaMinus r * radialU g r) = 0 →
      (∫ r : ℝ, bubbleRadialEnergyDerivative r * deriv (radialU f) r
        ∂halfLineMeasure) = 0 →
      compactTwoChannelGap *
        ((∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) +
          ∫ r : ℝ, (deriv (radialU g) r) ^ 2 ∂halfLineMeasure) ≤
        compactTwoChannelProfileForm f g) := by
  refine ⟨scale_gap_pos, joint_gap_pos, real_compact_gap, joint_compact_gap, ?_⟩
  intro f g hf hg hfm hgm hscale hphase hnegative
  have hq : scaleCompactTest (smoothToRadialDotH1 f hfm) = 0 := by
    rw [physicalScaleNormalization_certified.2.2.2.2.2.2.1 f hf hfm]
    exact hscale
  have hp : phaseCompactTest (smoothToRadialDotH1 g hgm) = 0 := by
    rw [actualCompactPhaseSlice_certified.2.2.1 g hg hgm]
    exact hphase
  have hn : inner ℝ fullBubbleRadialEnergyL2 (smoothToRadialDotH1 f hfm) = 0 := by
    rw [phaseBubble_coordinate_pairing f hfm]
    exact hnegative
  have h := joint_compact_gap (smoothToRadialDotH1 f hfm)
    (smoothToRadialDotH1 g hgm) hq hp hn
  rw [smoothRadialEnergy_coordinate_norm_sq f hfm,
    smoothRadialEnergy_coordinate_norm_sq g hgm,
    ← actual_profile_form f g hf hg hfm hgm] at h
  exact h

end HBL.Modulation.Monopole
