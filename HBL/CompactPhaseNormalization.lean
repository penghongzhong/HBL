import HBL.PhaseEnergyInverse
import HBL.ThresholdTestExistence
import HBL.RadialEnergyHilbertBridge

/-!
The original compact phase test, not the energy-orthogonal gauge.

The test is the previously constructed normalized smooth bump. Its action
on the actual bubble is proved to be one. The already proved 4/5 phase
gap is transferred to this genuine compact-test slice, including the
physical gradient form on the smooth upper-supported core. A bounded
inverse normalized by the same test is constructed from the existing
orthogonal inverse. No invariant zero-centre splitting is used.

This does not construct a Hamilton evolution group, a generator inverse,
or the completed physical Sobolev identification.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- The actual normalized compact phase test on full half-line energy. -/
def phaseCompactTest : FullRadialEnergyL2 →L[ℝ] ℝ :=
  (energyThresholdDual (Real.exp 1) (Real.exp_pos 1).le
    normalizedZetaMinus normalizedZetaMinus_contDiff_infty.continuous).comp
      (fullToFiniteRadialEnergy (Real.exp 1))

private theorem compactTest_on_core
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hm : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    phaseCompactTest (smoothToRadialDotH1 f hm) =
      ∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaMinus r * radialU f r := by
  change energyThresholdDual (Real.exp 1) (Real.exp_pos 1).le
    normalizedZetaMinus normalizedZetaMinus_contDiff_infty.continuous
      (fullToFiniteRadialEnergy (Real.exp 1) (smoothToRadialDotH1 f hm)) = _
  rw [smoothToRadialDotH1_restrict (Real.exp 1) (Real.exp_pos 1).le f hf hm,
    energyThresholdDual_on_radialCore]

private theorem compactTest_bubble :
    phaseCompactTest fullBubbleRadialEnergyL2 = 1 := by
  rw [← smoothBubbleToRadialDotH1_eq,
    compactTest_on_core bubble bubble_contDiff radialU_bubble_deriv_memLp]
  simpa only [radialResonanceMinus, radialU] using normalizedZetaMinus_normalized

/-- Quantified loss from energy orthogonality to the actual compact test. -/
def phaseCompactLoss : ℝ :=
  1 + ‖phaseCompactTest‖ * ‖fullBubbleRadialEnergyL2‖

def phaseCompactGap : ℝ := (4 / 5 : ℝ) / phaseCompactLoss ^ 2

private theorem compactLoss_pos : 0 < phaseCompactLoss := by
  unfold phaseCompactLoss
  positivity

private theorem compactGap_pos : 0 < phaseCompactGap := by
  unfold phaseCompactGap
  exact div_pos (by norm_num) (sq_pos_of_pos compactLoss_pos)

/-- This is an oblique gauge projection, not a spectral projection. -/
def phaseCompactProjection : FullRadialEnergyL2 →L[ℝ] FullRadialEnergyL2 :=
  ContinuousLinearMap.id ℝ FullRadialEnergyL2 -
    phaseCompactTest.smulRight fullBubbleRadialEnergyL2

private theorem compactProjection_test (q : FullRadialEnergyL2) :
    phaseCompactTest (phaseCompactProjection q) = 0 := by
  change phaseCompactTest
    (q - phaseCompactTest q • fullBubbleRadialEnergyL2) = 0
  rw [map_sub, map_smul, compactTest_bubble]
  simp

private theorem compactProjection_action (q : FullRadialEnergyL2) :
    weightedVolterraAMinus (phaseCompactProjection q) = weightedVolterraAMinus q := by
  change weightedVolterraAMinus
    (q - phaseCompactTest q • fullBubbleRadialEnergyL2) = _
  rw [map_sub, map_smul, weightedVolterraAMinus_bubble_zero, smul_zero, sub_zero]

private theorem compactProjection_bound (q : FullRadialEnergyL2) :
    ‖phaseCompactProjection q‖ ≤ phaseCompactLoss * ‖q‖ := by
  change ‖q - phaseCompactTest q • fullBubbleRadialEnergyL2‖ ≤ _
  calc
    ‖q - phaseCompactTest q • fullBubbleRadialEnergyL2‖ ≤
        ‖q‖ + ‖phaseCompactTest q • fullBubbleRadialEnergyL2‖ := norm_sub_le _ _
    _ = ‖q‖ + ‖phaseCompactTest q‖ * ‖fullBubbleRadialEnergyL2‖ := by
      rw [norm_smul]
    _ ≤ ‖q‖ + (‖phaseCompactTest‖ * ‖q‖) * ‖fullBubbleRadialEnergyL2‖ :=
      add_le_add_left (mul_le_mul_of_nonneg_right (phaseCompactTest.le_opNorm q)
        (norm_nonneg _)) _
    _ = phaseCompactLoss * ‖q‖ := by unfold phaseCompactLoss; ring

private theorem compactSlice_gap (q : FullRadialEnergyL2)
    (hq : phaseCompactTest q = 0) :
    phaseCompactGap * ‖q‖ ^ 2 ≤ inner ℝ (weightedVolterraAMinus q) q := by
  let w := fullBubbleRadialEnergyL2
  let c : ℝ := inner ℝ w q / inner ℝ w w
  let r : FullRadialEnergyL2 := q - c • w
  have hw : 0 < inner ℝ w w := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr phaseBubble_energy_ne_zero)
  have hrorth : inner ℝ fullBubbleRadialEnergyL2 r = 0 := by
    change inner ℝ w (q - c • w) = 0
    rw [inner_sub_right, real_inner_smul_right]
    dsimp only [c]
    rw [div_mul_cancel₀ _ (ne_of_gt hw), sub_self]
  have hrtest : phaseCompactTest r = -c := by
    change phaseCompactTest (q - c • fullBubbleRadialEnergyL2) = -c
    rw [map_sub, map_smul, hq, compactTest_bubble]
    simp
  have hqrep : q = phaseCompactProjection r := by
    change q = r - phaseCompactTest r • w
    rw [hrtest, neg_smul, sub_neg_eq_add]
    dsimp only [r]
    abel
  have hAr : weightedVolterraAMinus r = weightedVolterraAMinus q := by
    change weightedVolterraAMinus (q - c • fullBubbleRadialEnergyL2) = _
    rw [map_sub, map_smul, weightedVolterraAMinus_bubble_zero, smul_zero, sub_zero]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    weightedVolterraAMinus_selfAdjoint
  have hcross : inner ℝ (weightedVolterraAMinus q) w = 0 := by
    rw [hsym q w]
    change inner ℝ q (weightedVolterraAMinus fullBubbleRadialEnergyL2) = 0
    rw [weightedVolterraAMinus_bubble_zero, inner_zero_right]
  have hform : inner ℝ (weightedVolterraAMinus r) r =
      inner ℝ (weightedVolterraAMinus q) q := by
    rw [hAr]
    dsimp only [r]
    rw [inner_sub_right, real_inner_smul_right, hcross, mul_zero, sub_zero]
  have hgap := weightedVolterraAMinus_tail_coercive r
    ((phaseBubble_orthogonal_iff r).mp hrorth)
  rw [hform] at hgap
  have hnorm : ‖q‖ ≤ phaseCompactLoss * ‖r‖ := by
    calc
      ‖q‖ = ‖phaseCompactProjection r‖ := congrArg norm hqrep
      _ ≤ phaseCompactLoss * ‖r‖ := compactProjection_bound r
  have hsquare : ‖q‖ ^ 2 ≤ phaseCompactLoss ^ 2 * ‖r‖ ^ 2 := by
    have hproduct := mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg (mul_nonneg compactLoss_pos.le (norm_nonneg r)) (norm_nonneg q))
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hgap (sq_nonneg phaseCompactLoss)
  unfold phaseCompactGap
  rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos compactLoss_pos)]
  nlinarith

/-- Complete actual compact-test coercivity, including the physical 3D
phase form on the supported C1 core. The compact gauge is not assumed
energy orthogonal to W, and its normalization is proved internally. -/
theorem actualCompactPhaseSlice_certified :
    phaseCompactTest fullBubbleRadialEnergyL2 = 1 ∧
    0 < phaseCompactGap ∧
    (∀ (f : ℝ → ℝ) (_hf : ContDiff ℝ 1 f)
      (hm : MemLp (deriv (radialU f)) 2 halfLineMeasure),
      phaseCompactTest (smoothToRadialDotH1 f hm) =
        ∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaMinus r * radialU f r) ∧
    (∀ q : FullRadialEnergyL2, phaseCompactTest q = 0 →
      phaseCompactGap * ‖q‖ ^ 2 ≤ inner ℝ (weightedVolterraAMinus q) q) ∧
    (∀ (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (R : ℝ) (hR : 0 ≤ R)
      (hcut : ∀ r : ℝ, R ≤ r → f r = 0),
      (∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaMinus r * radialU f r) = 0 →
      phaseCompactGap * (∫ x : PhysicalRadialSpace3,
        ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) ≤
        physicalRadial3PhaseQuadratic f) := by
  refine ⟨compactTest_bubble, compactGap_pos, compactTest_on_core,
    compactSlice_gap, ?_⟩
  intro f hf R hR hcut htest
  let hm := radialU_deriv_memLp_of_upperSupport f hf R hR hcut
  have hq : phaseCompactTest (smoothToRadialDotH1 f hm) = 0 := by
    rw [compactTest_on_core f hf hm]
    exact htest
  have hb := mul_le_mul_of_nonneg_left
    (compactSlice_gap (smoothToRadialDotH1 f hm) hq)
    (show (0 : ℝ) ≤ 4 * Real.pi by positivity)
  rw [physicalRadial3_gradient_coordinate_of_upperSupport f hf R hR hcut,
    physicalRadial3_phase_core_eq_volterra f hf R hR hcut]
  nlinarith only [hb]

/-- Actual inverse normalized by the fixed compact test rather than by
orthogonality. The source still satisfies the necessary phase compatibility. -/
def phaseCompactInverse : PhaseEnergyComplement →L[ℝ] FullRadialEnergyL2 :=
  phaseCompactProjection.comp
    (PhaseEnergyComplement.subtypeL.comp phaseEnergyInverse)

private theorem compactInverse_right (f : PhaseEnergyComplement) :
    weightedVolterraAMinus (phaseCompactInverse f) = (f : FullRadialEnergyL2) := by
  change weightedVolterraAMinus
    (phaseCompactProjection (phaseEnergyInverse f : FullRadialEnergyL2)) = _
  rw [compactProjection_action]
  have h := congrArg Subtype.val (phaseEnergyInverse_certified.2.1 f)
  exact h

private theorem compactInverse_test (f : PhaseEnergyComplement) :
    phaseCompactTest (phaseCompactInverse f) = 0 :=
  compactProjection_test (phaseEnergyInverse f : FullRadialEnergyL2)

private theorem compactInverse_unique (f : PhaseEnergyComplement)
    (x : FullRadialEnergyL2)
    (hx : weightedVolterraAMinus x = (f : FullRadialEnergyL2))
    (ht : phaseCompactTest x = 0) : x = phaseCompactInverse f := by
  have hk : x - phaseCompactInverse f ∈ weightedVolterraAMinus.ker := by
    change weightedVolterraAMinus (x - phaseCompactInverse f) = 0
    rw [map_sub, hx, compactInverse_right, sub_self]
  rw [weightedVolterraAMinus_kernel_eq_bubble_span] at hk
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hk
  have hc0 : c = 0 := by
    have h := congrArg phaseCompactTest hc
    rw [map_smul, compactTest_bubble, map_sub, ht, compactInverse_test] at h
    simpa using h
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

private theorem compactInverse_norm :
    ‖phaseCompactInverse‖ ≤ phaseCompactLoss * (5 / 4 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg compactLoss_pos.le (by norm_num))
  intro f
  have hinv := (phaseEnergyInverse.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right phaseEnergyInverse_certified.2.2.2.1 (norm_nonneg f))
  calc
    ‖phaseCompactInverse f‖ ≤ phaseCompactLoss * ‖phaseEnergyInverse f‖ :=
      compactProjection_bound (phaseEnergyInverse f : FullRadialEnergyL2)
    _ ≤ phaseCompactLoss * ((5 / 4 : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hinv compactLoss_pos.le
    _ = (phaseCompactLoss * (5 / 4 : ℝ)) * ‖f‖ := by ring

/-- Complete compact-normalized phase inverse: the oblique gauge keeps
the actual operator action, solves every compatible source uniquely,
has a quantified bound and carries C1 source paths to C1 solutions.
It is not an inverse of the Hamilton generator or a zero-centre Sylvester map. -/
theorem actualCompactPhaseInverse_certified :
    (∀ q : FullRadialEnergyL2,
      phaseCompactTest (phaseCompactProjection q) = 0 ∧
      weightedVolterraAMinus (phaseCompactProjection q) = weightedVolterraAMinus q) ∧
    (∀ f : PhaseEnergyComplement,
      weightedVolterraAMinus (phaseCompactInverse f) = (f : FullRadialEnergyL2) ∧
      phaseCompactTest (phaseCompactInverse f) = 0 ∧
      ∀ x : FullRadialEnergyL2,
        weightedVolterraAMinus x = (f : FullRadialEnergyL2) →
        phaseCompactTest x = 0 → x = phaseCompactInverse f) ∧
    ‖phaseCompactInverse‖ ≤ phaseCompactLoss * (5 / 4 : ℝ) ∧
    (∀ F : ℝ → PhaseEnergyComplement,
      ContDiff ℝ 1 F → ContDiff ℝ 1 (fun s => phaseCompactInverse (F s))) := by
  refine ⟨(fun q => ⟨compactProjection_test q, compactProjection_action q⟩),
    (fun f => ⟨compactInverse_right f, compactInverse_test f, compactInverse_unique f⟩),
    compactInverse_norm, ?_⟩
  intro F hF
  exact phaseCompactInverse.contDiff.comp hF

end HBL.Modulation.Monopole
