import HBL.WeightedFreeGreen
import Mathlib.MeasureTheory.Integral.Prod

/-!
The actual weighted Volterra kernel on the positive half-line.

Its overlap integral is the existing weighted free Green kernel.  The
diagonal overlap and the existing integrable Green majorant establish
product square integrability, without an assumed operator factorization.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail

/-- The weighted Volterra kernel for integration from zero to the output radius. -/
def weightedVolterraKernel (r s : ℝ) : ℝ :=
  if 0 < s ∧ s < r then (1 + r ^ 2)⁻¹ else 0

theorem weightedVolterraKernel_measurable :
    Measurable (Function.uncurry weightedVolterraKernel) := by
  unfold weightedVolterraKernel Function.uncurry
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  exact Measurable.ite hset
    (measurable_const.add (measurable_fst.pow_const 2)).inv measurable_const

theorem weightedVolterraKernel_nonneg (r s : ℝ) :
    0 ≤ weightedVolterraKernel r s := by
  unfold weightedVolterraKernel
  split_ifs <;> positivity

private theorem weightedVolterraKernel_mul_indicator (r rho s : ℝ) :
    weightedVolterraKernel r s * weightedVolterraKernel rho s =
      (Ioo (0 : ℝ) (min r rho)).indicator
        (fun _ => (1 + r ^ 2)⁻¹ * (1 + rho ^ 2)⁻¹) s := by
  by_cases hs : 0 < s
  · by_cases hr : s < r
    · by_cases hrho : s < rho <;>
        simp [weightedVolterraKernel, Set.indicator, lt_min_iff, hs, hr, hrho]
    · simp [weightedVolterraKernel, Set.indicator, lt_min_iff, hs, hr]
  · simp [weightedVolterraKernel, Set.indicator, hs]

/-- The actual overlap of two Volterra rows is the actual weighted Green kernel. -/
theorem weightedVolterraKernel_overlap
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho) :
    (∫ s : ℝ, weightedVolterraKernel r s * weightedVolterraKernel rho s
      ∂halfLineMeasure) = weightedFreeGreen r rho := by
  simp_rw [weightedVolterraKernel_mul_indicator]
  rw [integral_indicator measurableSet_Ioo]
  change (∫ s : ℝ, (1 + r ^ 2)⁻¹ * (1 + rho ^ 2)⁻¹
      ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Ioo 0 (min r rho)))) = _
  rw [Measure.restrict_restrict_of_subset Ioo_subset_Ioi_self,
    setIntegral_const, Real.volume_real_Ioo_of_le (le_min hr.le hrho.le),
    sub_zero, smul_eq_mul]
  unfold weightedFreeGreen
  ring

private theorem weightedVolterraKernel_row_sq_integrable (r : ℝ) :
    Integrable (fun s : ℝ => weightedVolterraKernel r s ^ 2) halfLineMeasure := by
  have hconst : IntegrableOn
      (fun _ : ℝ => (1 + r ^ 2)⁻¹ * (1 + r ^ 2)⁻¹)
      (Ioo (0 : ℝ) (min r r)) volume :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hind := hconst.integrable_indicator measurableSet_Ioo
  have heq : (fun s : ℝ => weightedVolterraKernel r s ^ 2) =
      (Ioo (0 : ℝ) (min r r)).indicator
        (fun _ => (1 + r ^ 2)⁻¹ * (1 + r ^ 2)⁻¹) := by
    funext s
    rw [pow_two, weightedVolterraKernel_mul_indicator]
  rw [heq]
  exact hind.integrableOn

private theorem weightedVolterraKernel_sq_integrable :
    Integrable (fun p : ℝ × ℝ => weightedVolterraKernel p.1 p.2 ^ 2)
      (halfLineMeasure.prod halfLineMeasure) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => weightedVolterraKernel p.1 p.2 ^ 2)
      (halfLineMeasure.prod halfLineMeasure) :=
    (weightedVolterraKernel_measurable.pow_const 2).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · exact Filter.Eventually.of_forall weightedVolterraKernel_row_sq_integrable
  · have hmajor : Integrable freeGreenMajorant halfLineMeasure :=
      freeGreenMajorant_integrable.integrableOn
    refine hmajor.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    calc
      freeGreenMajorant r = weightedFreeGreen r r := by
        unfold freeGreenMajorant weightedFreeGreen
        rw [abs_of_pos hr, min_self]
        ring
      _ = ∫ s : ℝ, weightedVolterraKernel r s * weightedVolterraKernel r s
          ∂halfLineMeasure := (weightedVolterraKernel_overlap r r hr hr).symm
      _ = ∫ s : ℝ, ‖weightedVolterraKernel r s ^ 2‖ ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards with s
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]

/-- The actual Volterra kernel is square integrable on the product half-line. -/
theorem weightedVolterraKernel_memLp :
    MemLp (Function.uncurry weightedVolterraKernel) 2
      (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq
    weightedVolterraKernel_measurable.aestronglyMeasurable).2
  exact weightedVolterraKernel_sq_integrable

end HBL.Modulation.Monopole
