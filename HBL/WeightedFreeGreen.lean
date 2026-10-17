import HBL.HartreeKernelShortRange

/-!
The weighted zero-slope Green kernel for the free half-line Laplacian.

With the endpoint weight `q ↦ q / (1+r²)`, the Dirichlet Green kernel
`min r ρ` becomes

  `min r ρ / ((1+r²)(1+ρ²))`.

This file proves directly that this kernel is symmetric and belongs to
product L2 on the positive half-line.  No compactness assertion is inserted
as an external premise: the kernel is connected to the actual bounded
operator constructed in `L2KernelOperator`.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel

/-- The one-variable integrable majorant for the squared weighted Green
kernel. -/
def freeGreenMajorant (r : ℝ) : ℝ :=
  |r| * (1 + r ^ 2)⁻¹ ^ 2

theorem freeGreenMajorant_continuous :
    Continuous freeGreenMajorant := by
  unfold freeGreenMajorant
  have hden : Continuous (fun r : ℝ => 1 + r ^ 2) := by fun_prop
  exact continuous_abs.mul
    ((hden.inv₀ (fun r => by positivity)).pow 2)

theorem freeGreenMajorant_nonneg (r : ℝ) :
    0 ≤ freeGreenMajorant r := by
  unfold freeGreenMajorant
  positivity

theorem freeGreenMajorant_le_cauchy (r : ℝ) :
    freeGreenMajorant r ≤ (1 + r ^ 2)⁻¹ := by
  have hden : 0 < 1 + r ^ 2 := by positivity
  have habs : |r| ≤ 1 + r ^ 2 := by
    nlinarith [sq_nonneg (|r| - 1 / 2), sq_abs r]
  calc
    freeGreenMajorant r = |r| * (1 + r ^ 2)⁻¹ ^ 2 := rfl
    _ ≤ (1 + r ^ 2) * (1 + r ^ 2)⁻¹ ^ 2 := by
      exact mul_le_mul_of_nonneg_right habs (sq_nonneg _)
    _ = (1 + r ^ 2)⁻¹ := by
      field_simp

theorem freeGreenMajorant_integrable :
    Integrable freeGreenMajorant := by
  refine integrable_inv_one_add_sq.mono'
    freeGreenMajorant_continuous.aestronglyMeasurable ?_
  filter_upwards with r
  rw [Real.norm_eq_abs, abs_of_nonneg (freeGreenMajorant_nonneg r)]
  exact freeGreenMajorant_le_cauchy r

/-- The free Dirichlet Green kernel after conjugating by the endpoint weight
`1+r²`. -/
def weightedFreeGreen (r rho : ℝ) : ℝ :=
  min r rho * (1 + r ^ 2)⁻¹ * (1 + rho ^ 2)⁻¹

theorem weightedFreeGreen_symm (r rho : ℝ) :
    weightedFreeGreen r rho = weightedFreeGreen rho r := by
  unfold weightedFreeGreen
  rw [min_comm]
  ring

theorem weightedFreeGreen_uncurry_continuous :
    Continuous (Function.uncurry weightedFreeGreen) := by
  unfold weightedFreeGreen Function.uncurry
  have hr : Continuous (fun p : ℝ × ℝ => 1 + p.1 ^ 2) := by fun_prop
  have hρ : Continuous (fun p : ℝ × ℝ => 1 + p.2 ^ 2) := by fun_prop
  exact ((continuous_fst.min continuous_snd).mul
    (hr.inv₀ (fun p => by positivity))).mul
      (hρ.inv₀ (fun p => by positivity))

theorem min_sq_le_mul_of_pos {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    min r rho ^ 2 ≤ r * rho := by
  have hm0 : 0 ≤ min r rho := (lt_min hr hrho).le
  have hmr : min r rho ≤ r := min_le_left _ _
  have hmρ : min r rho ≤ rho := min_le_right _ _
  nlinarith

theorem weightedFreeGreen_sq_le_majorant
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    weightedFreeGreen r rho ^ 2 ≤
      freeGreenMajorant r * freeGreenMajorant rho := by
  have hw0 : 0 ≤ (1 + r ^ 2)⁻¹ ^ 2 * (1 + rho ^ 2)⁻¹ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmin := min_sq_le_mul_of_pos hr hrho
  unfold weightedFreeGreen freeGreenMajorant
  rw [abs_of_pos hr, abs_of_pos hrho]
  calc
    (min r rho * (1 + r ^ 2)⁻¹ * (1 + rho ^ 2)⁻¹) ^ 2 =
        min r rho ^ 2 *
          ((1 + r ^ 2)⁻¹ ^ 2 * (1 + rho ^ 2)⁻¹ ^ 2) := by ring
    _ ≤ (r * rho) *
          ((1 + r ^ 2)⁻¹ ^ 2 * (1 + rho ^ 2)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_right hmin hw0
    _ = (r * (1 + r ^ 2)⁻¹ ^ 2) *
          (rho * (1 + rho ^ 2)⁻¹ ^ 2) := by ring

theorem weightedFreeGreen_sq_integrable :
    Integrable (fun p : ℝ × ℝ => weightedFreeGreen p.1 p.2 ^ 2)
      (HBL.Modulation.AffineTail.halfLineMeasure.prod
        HBL.Modulation.AffineTail.halfLineMeasure) := by
  rw [HBL.Modulation.AffineTail.halfLineMeasure, Measure.prod_restrict]
  have hmajor : IntegrableOn
      (fun p : ℝ × ℝ => freeGreenMajorant p.1 * freeGreenMajorant p.2)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (volume.prod volume) :=
    (freeGreenMajorant_integrable.mul_prod
      freeGreenMajorant_integrable).integrableOn
  refine hmajor.mono'
    ((weightedFreeGreen_uncurry_continuous.pow 2).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact weightedFreeGreen_sq_le_majorant hp.1 hp.2

theorem weightedFreeGreen_memLp_two :
    MemLp (Function.uncurry weightedFreeGreen) 2
      (HBL.Modulation.AffineTail.halfLineMeasure.prod
        HBL.Modulation.AffineTail.halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq
    weightedFreeGreen_uncurry_continuous.aestronglyMeasurable).2
  exact weightedFreeGreen_sq_integrable

/-- Product-L2 realization of the weighted free Green kernel. -/
def weightedFreeGreenL2 :
    RealKernelL2 HBL.Modulation.AffineTail.halfLineMeasure :=
  weightedFreeGreen_memLp_two.toLp (Function.uncurry weightedFreeGreen)

theorem weightedFreeGreenL2_ae :
    (weightedFreeGreenL2 : ℝ × ℝ → ℝ) =ᵐ[
      HBL.Modulation.AffineTail.halfLineMeasure.prod
        HBL.Modulation.AffineTail.halfLineMeasure]
      Function.uncurry weightedFreeGreen :=
  weightedFreeGreen_memLp_two.coeFn_toLp

/-- The actual bounded L2 operator associated with the weighted free Green
kernel. -/
def weightedFreeGreenOperator :
    RealL2 HBL.Modulation.AffineTail.halfLineMeasure →L[ℝ]
      RealL2 HBL.Modulation.AffineTail.halfLineMeasure :=
  operator weightedFreeGreenL2

theorem weightedFreeGreenOperator_kernel_certificate :
    IsHilbertSchmidtKernelOperator weightedFreeGreenOperator
      weightedFreeGreenL2 :=
  operator_isHilbertSchmidtKernelOperator weightedFreeGreenL2

/-- The doubly weighted free radial Green operator is compact. -/
theorem weightedFreeGreenOperator_compact :
    IsCompactOperator weightedFreeGreenOperator :=
  HBL.L2Kernel.operator_isCompactOperator weightedFreeGreenL2

end HBL.Modulation.Monopole
