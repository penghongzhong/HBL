import HBL.RealEnergyInverse
import HBL.ThresholdTestExistence
import HBL.RadialEnergyHilbertBridge

/-!
R10 connects the actual real energy inverse to the physical scale
coordinate (r Lambda W)' and to the manuscript's original compact test.

The scale coordinate is identified by the proved adjoint tail formula:
V* (15 x0) = (r Lambda W)'. Its L2 membership is a conclusion, not an
additional premise. The compact normalization uses the already constructed
normalizedZetaPlus. Negative directions are retained. This is not an
inverse for the unbounded Hamilton generator and does not claim the
completed physical Sobolev realization or any evolution construction.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem scaleVector_actual_derivative :
    (weightedVolterraScaleVector : ℝ → ℝ) =ᵐ[halfLineMeasure]
      deriv (radialU (dilationGenerator bubble)) := by
  have hf : (((15 : ℝ) • weightedScaleResonanceL2 : RealL2 halfLineMeasure) :
      ℝ → ℝ) =ᵐ[halfLineMeasure] (fun r => 15 * weightedScaleResonance r) := by
    filter_upwards [Lp.coeFn_smul (15 : ℝ) weightedScaleResonanceL2,
      weightedScaleResonanceL2_ae] with r hsmul hscale
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul, hscale]
  change (weightedVolterraScaleVector : ℝ → ℝ) =ᵐ[halfLineMeasure]
    deriv resonancePlus
  unfold weightedVolterraScaleVector
  rw [weightedPotentialOperator_scale_eigen]
  refine (weightedVolterraOperator_adjoint_ae_pointwise
    ((15 : ℝ) • weightedScaleResonanceL2)).trans ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [← weightedScaleGreenSource_tail s]
  apply integral_congr_ae
  have htail := ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi hs.le) hf
  filter_upwards [htail] with r hr
  rw [hr, weightedScaleResonance_closed]
  unfold weightedScaleGreenSource
  ring

private theorem scaleProfile_energy_memLp :
    MemLp (deriv (radialU (dilationGenerator bubble))) 2 halfLineMeasure := by
  exact MemLp.ae_eq scaleVector_actual_derivative (Lp.memLp weightedVolterraScaleVector)

private theorem scaleProfile_contDiff : ContDiff ℝ 1 (dilationGenerator bubble) := by
  have hd : ContDiff ℝ ∞ (deriv bubble) :=
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2
  have h : ContDiff ℝ ∞ (dilationGenerator bubble) := by
    unfold dilationGenerator
    exact (bubble_contDiff_infty.div_const 2).add (contDiff_id.mul hd)
  exact h.of_le (by norm_num)

private theorem scaleProfile_coordinate
    (hm : MemLp (deriv (radialU (dilationGenerator bubble))) 2 halfLineMeasure) :
    smoothToRadialDotH1 (dilationGenerator bubble) hm = weightedVolterraScaleVector := by
  apply Lp.ext
  exact (smoothToRadialDotH1_ae (dilationGenerator bubble) hm).trans
    scaleVector_actual_derivative.symm

/-- The manuscript's actual compact scale test, not an energy inner product. -/
def scaleCompactTest : FullRadialEnergyL2 →L[ℝ] ℝ :=
  (energyThresholdDual (Real.exp 1) (Real.exp_pos 1).le
    normalizedZetaPlus normalizedZetaPlus_contDiff_infty.continuous).comp
      (fullToFiniteRadialEnergy (Real.exp 1))

private theorem scaleTest_on_core
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hm : MemLp (deriv (radialU f)) 2 halfLineMeasure) :
    scaleCompactTest (smoothToRadialDotH1 f hm) =
      ∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaPlus r * radialU f r := by
  change energyThresholdDual (Real.exp 1) (Real.exp_pos 1).le
    normalizedZetaPlus normalizedZetaPlus_contDiff_infty.continuous
      (fullToFiniteRadialEnergy (Real.exp 1) (smoothToRadialDotH1 f hm)) = _
  rw [smoothToRadialDotH1_restrict (Real.exp 1) (Real.exp_pos 1).le f hf hm,
    energyThresholdDual_on_radialCore]

private theorem scaleTest_normalized : scaleCompactTest weightedVolterraScaleVector = 1 := by
  rw [← scaleProfile_coordinate scaleProfile_energy_memLp,
    scaleTest_on_core (dilationGenerator bubble) scaleProfile_contDiff
      scaleProfile_energy_memLp]
  simpa only [radialResonancePlus, radialU] using normalizedZetaPlus_normalized

private theorem scaleVector_zero : weightedVolterraAPlus weightedVolterraScaleVector = 0 := by
  have hm : weightedVolterraScaleVector ∈ weightedVolterraAPlus.ker := by
    rw [weightedVolterraAPlus_kernel_eq_span]
    exact Submodule.subset_span (by simp)
  exact hm

private theorem physicalScale_compatibility (f : FullRadialEnergyL2) :
    (∃ x : FullRadialEnergyL2, weightedVolterraAPlus x = f) ↔
      inner ℝ weightedVolterraScaleVector f = 0 := by
  change f ∈ weightedVolterraAPlus.range ↔ _
  rw [realEnergyInverse_certified.1]
  change f ∈ weightedVolterraAPlus.kerᗮ ↔ _
  rw [weightedVolterraAPlus_kernel_eq_span]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

/-- Only a gauge projection; no commutation with a Hamilton generator is claimed. -/
def scaleCompactProjection : FullRadialEnergyL2 →L[ℝ] FullRadialEnergyL2 :=
  ContinuousLinearMap.id ℝ FullRadialEnergyL2 -
    scaleCompactTest.smulRight weightedVolterraScaleVector

def scaleCompactLoss : ℝ := 1 + ‖scaleCompactTest‖ * ‖weightedVolterraScaleVector‖

private theorem scaleLoss_pos : 0 < scaleCompactLoss := by
  unfold scaleCompactLoss
  positivity

private theorem scaleProjection_test (q : FullRadialEnergyL2) :
    scaleCompactTest (scaleCompactProjection q) = 0 := by
  change scaleCompactTest (q - scaleCompactTest q • weightedVolterraScaleVector) = 0
  rw [map_sub, map_smul, scaleTest_normalized]
  simp

private theorem scaleProjection_action (q : FullRadialEnergyL2) :
    weightedVolterraAPlus (scaleCompactProjection q) = weightedVolterraAPlus q := by
  change weightedVolterraAPlus (q - scaleCompactTest q • weightedVolterraScaleVector) = _
  rw [map_sub, map_smul, scaleVector_zero, smul_zero, sub_zero]

private theorem scaleProjection_bound (q : FullRadialEnergyL2) :
    ‖scaleCompactProjection q‖ ≤ scaleCompactLoss * ‖q‖ := by
  change ‖q - scaleCompactTest q • weightedVolterraScaleVector‖ ≤ _
  calc
    ‖q - scaleCompactTest q • weightedVolterraScaleVector‖ ≤
        ‖q‖ + ‖scaleCompactTest q • weightedVolterraScaleVector‖ := norm_sub_le _ _
    _ = ‖q‖ + ‖scaleCompactTest q‖ * ‖weightedVolterraScaleVector‖ := by rw [norm_smul]
    _ ≤ ‖q‖ + (‖scaleCompactTest‖ * ‖q‖) * ‖weightedVolterraScaleVector‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (scaleCompactTest.le_opNorm q)
        (norm_nonneg _))
    _ = scaleCompactLoss * ‖q‖ := by unfold scaleCompactLoss; ring

/-- Concrete real inverse normalized by the original compact scale test. -/
def scaleCompactInverse : RealEnergyComplement →L[ℝ] FullRadialEnergyL2 :=
  scaleCompactProjection.comp (RealEnergyComplement.subtypeL.comp realEnergyInverse)

private theorem scaleInverse_right (f : RealEnergyComplement) :
    weightedVolterraAPlus (scaleCompactInverse f) = (f : FullRadialEnergyL2) := by
  change weightedVolterraAPlus
    (scaleCompactProjection (realEnergyInverse f : FullRadialEnergyL2)) = _
  rw [scaleProjection_action]
  exact congrArg Subtype.val (realEnergyInverse_certified.2.2.1 f)

private theorem scaleInverse_test (f : RealEnergyComplement) :
    scaleCompactTest (scaleCompactInverse f) = 0 :=
  scaleProjection_test (realEnergyInverse f : FullRadialEnergyL2)

private theorem scaleInverse_unique (f : RealEnergyComplement) (x : FullRadialEnergyL2)
    (hx : weightedVolterraAPlus x = (f : FullRadialEnergyL2))
    (ht : scaleCompactTest x = 0) : x = scaleCompactInverse f := by
  have hk : x - scaleCompactInverse f ∈ weightedVolterraAPlus.ker := by
    change weightedVolterraAPlus (x - scaleCompactInverse f) = 0
    rw [map_sub, hx, scaleInverse_right, sub_self]
  rw [weightedVolterraAPlus_kernel_eq_span] at hk
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hk
  have hc0 : c = 0 := by
    have h := congrArg scaleCompactTest hc
    rw [map_smul, scaleTest_normalized, map_sub, ht, scaleInverse_test] at h
    simpa using h
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

private theorem scaleInverse_norm :
    ‖scaleCompactInverse‖ ≤ scaleCompactLoss * (58 / 33 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg scaleLoss_pos.le (by norm_num))
  intro f
  have hi := (realEnergyInverse.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right realEnergyInverse_certified.2.2.2.2.1 (norm_nonneg f))
  calc
    ‖scaleCompactInverse f‖ ≤ scaleCompactLoss * ‖realEnergyInverse f‖ :=
      scaleProjection_bound (realEnergyInverse f : FullRadialEnergyL2)
    _ ≤ scaleCompactLoss * ((58 / 33 : ℝ)) * ‖f‖ := by
      calc
        scaleCompactLoss * ‖realEnergyInverse f‖ ≤
            scaleCompactLoss * ((58 / 33 : ℝ) * ‖f‖) :=
          mul_le_mul_of_nonneg_left hi scaleLoss_pos.le
        _ = _ := by ring

/-- One complete R10 environment: physical scale identification, actual
compact normalization, source compatibility, and the uniquely normalized
bounded real inverse. No target conclusion is a hypothesis. -/
theorem physicalScaleNormalization_certified :
    MemLp (deriv (radialU (dilationGenerator bubble))) 2 halfLineMeasure ∧
    (∀ hm : MemLp (deriv (radialU (dilationGenerator bubble))) 2 halfLineMeasure,
      smoothToRadialDotH1 (dilationGenerator bubble) hm = weightedVolterraScaleVector) ∧
    weightedVolterraScaleVector ≠ 0 ∧
    weightedVolterraAPlus weightedVolterraScaleVector = 0 ∧
    weightedVolterraAPlus.ker = Submodule.span ℝ {weightedVolterraScaleVector} ∧
    scaleCompactTest weightedVolterraScaleVector = 1 ∧
    (∀ (f : ℝ → ℝ) (_hf : ContDiff ℝ 1 f)
      (hm : MemLp (deriv (radialU f)) 2 halfLineMeasure),
      scaleCompactTest (smoothToRadialDotH1 f hm) =
        ∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaPlus r * radialU f r) ∧
    (∀ f : FullRadialEnergyL2,
      (∃ x : FullRadialEnergyL2, weightedVolterraAPlus x = f) ↔
        inner ℝ weightedVolterraScaleVector f = 0) ∧
    (∀ f : RealEnergyComplement,
      weightedVolterraAPlus (scaleCompactInverse f) = (f : FullRadialEnergyL2) ∧
      scaleCompactTest (scaleCompactInverse f) = 0 ∧
      ∀ x : FullRadialEnergyL2,
        weightedVolterraAPlus x = (f : FullRadialEnergyL2) →
        scaleCompactTest x = 0 → x = scaleCompactInverse f) ∧
    ‖scaleCompactInverse‖ ≤ scaleCompactLoss * (58 / 33 : ℝ) ∧
    (∀ F : ℝ → RealEnergyComplement, ContDiff ℝ 1 F →
      ContDiff ℝ 1 (fun s => scaleCompactInverse (F s))) := by
  refine ⟨scaleProfile_energy_memLp, scaleProfile_coordinate,
    weightedVolterraScaleVector_ne_zero, scaleVector_zero,
    weightedVolterraAPlus_kernel_eq_span, scaleTest_normalized,
    scaleTest_on_core, physicalScale_compatibility,
    (fun f => ⟨scaleInverse_right f, scaleInverse_test f, scaleInverse_unique f⟩),
    scaleInverse_norm, ?_⟩
  intro F hF
  exact scaleCompactInverse.contDiff.comp hF

end HBL.Modulation.Monopole
