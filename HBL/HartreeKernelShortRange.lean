import HBL.L2KernelOperator
import HBL.AffineTailHartreeIntegrability

/-!
Full closure of the manuscript lemma on the short-range radial Hartree
kernel.  Besides the pointwise separated/diagonal bounds, this file proves
square integrability and constructs the actual bounded self-adjoint L2
operator from the kernel form.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- The half-line Lebesgue measure used by the conjugated radial operator. -/
abbrev halfLineMeasure : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-- The square weight supplied by one radial factor of the kernel. -/
def kernelSquareWeight (r : ℝ) : ℝ := bubble r ^ 6

/-- The square weight with the factor used to absorb the logarithmic
diagonal singularity. -/
def kernelSquareSqrtWeight (r : ℝ) : ℝ :=
  Real.sqrt r * kernelSquareWeight r

theorem kernelSquareWeight_nonneg (r : ℝ) :
    0 ≤ kernelSquareWeight r := by
  unfold kernelSquareWeight
  positivity

theorem kernelSquareSqrtWeight_nonneg (r : ℝ) :
    0 ≤ kernelSquareSqrtWeight r := by
  unfold kernelSquareSqrtWeight
  exact mul_nonneg (Real.sqrt_nonneg r) (kernelSquareWeight_nonneg r)

theorem kernelSquareWeight_closed (r : ℝ) :
    kernelSquareWeight r = (1 + r ^ 2)⁻¹ ^ 3 := by
  unfold kernelSquareWeight bubble
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [inv_pow, inv_pow]
  congr 1
  calc
    Real.sqrt (1 + r ^ 2) ^ 6 =
        (Real.sqrt (1 + r ^ 2) ^ 2) ^ 3 := by ring
    _ = (1 + r ^ 2) ^ 3 := by rw [hs2]

theorem kernelSquareWeight_le (r : ℝ) :
    kernelSquareWeight r ≤ (1 + r ^ 2)⁻¹ := by
  rw [kernelSquareWeight_closed]
  have h : (1 + r ^ 2)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
    nlinarith [sq_nonneg r]
  have hx : 0 ≤ (1 + r ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  calc
    (1 + r ^ 2)⁻¹ ^ 3 =
        (1 + r ^ 2)⁻¹ ^ 2 * (1 + r ^ 2)⁻¹ := by ring
    _ ≤ 1 ^ 2 * (1 + r ^ 2)⁻¹ := by
      gcongr
    _ = (1 + r ^ 2)⁻¹ := by ring

theorem kernelSquareSqrtWeight_le (r : ℝ) :
    kernelSquareSqrtWeight r ≤ (1 + r ^ 2)⁻¹ := by
  by_cases hr : 0 ≤ r
  · rw [kernelSquareSqrtWeight, kernelSquareWeight_closed]
    have hs2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
    have hsle : Real.sqrt r ≤ 1 + r ^ 2 := by
      by_cases h1 : r ≤ 1
      · have hs : Real.sqrt r ≤ 1 := by nlinarith [Real.sqrt_nonneg r]
        nlinarith [sq_nonneg r]
      · have hs : Real.sqrt r ≤ r := by
          nlinarith [Real.sqrt_nonneg r]
        nlinarith [sq_nonneg r]
    have hi : 0 ≤ (1 + r ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
    have hi1 : (1 + r ^ 2)⁻¹ ≤ 1 := by
      apply (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
      nlinarith [sq_nonneg r]
    calc
      Real.sqrt r * (1 + r ^ 2)⁻¹ ^ 3 ≤
          (1 + r ^ 2) * (1 + r ^ 2)⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_right hsle (by positivity)
      _ = (1 + r ^ 2)⁻¹ ^ 2 := by field_simp
      _ ≤ (1 + r ^ 2)⁻¹ := by nlinarith
  · have hs : Real.sqrt r = 0 :=
      Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hr)
    simp [kernelSquareSqrtWeight, hs]
    positivity

theorem kernelSquareWeight_continuous :
    Continuous kernelSquareWeight := by
  unfold kernelSquareWeight
  exact bubble_contDiff_infty.continuous.pow 6

theorem kernelSquareSqrtWeight_continuous :
    Continuous kernelSquareSqrtWeight := by
  unfold kernelSquareSqrtWeight
  exact Real.continuous_sqrt.mul kernelSquareWeight_continuous

theorem kernelSquareWeight_integrable :
    Integrable kernelSquareWeight := by
  refine integrable_inv_one_add_sq.mono'
    kernelSquareWeight_continuous.aestronglyMeasurable ?_
  filter_upwards with r
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelSquareWeight_nonneg r)]
  exact kernelSquareWeight_le r

theorem kernelSquareSqrtWeight_integrable :
    Integrable kernelSquareSqrtWeight := by
  refine integrable_inv_one_add_sq.mono'
    kernelSquareSqrtWeight_continuous.aestronglyMeasurable ?_
  filter_upwards with r
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelSquareSqrtWeight_nonneg r)]
  exact kernelSquareSqrtWeight_le r

theorem kernelSquareWeight_norm_le_one (r : ℝ) :
    ‖kernelSquareWeight r‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelSquareWeight_nonneg r)]
  exact (kernelSquareWeight_le r).trans <| by
    apply (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
    nlinarith [sq_nonneg r]

theorem kernelSquareSqrtWeight_norm_le_one (r : ℝ) :
    ‖kernelSquareSqrtWeight r‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelSquareSqrtWeight_nonneg r)]
  exact (kernelSquareSqrtWeight_le r).trans <| by
    apply (inv_le_one₀ (by positivity : 0 < 1 + r ^ 2)).2
    nlinarith [sq_nonneg r]

/-- A fourth-root logarithmic estimate; after squaring it leaves the
integrable singularity `|r-rho|^(-1/2)`. -/
theorem hartreeRadialLog_sq_sqrt_bound
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho) :
    hartreeRadialLog r rho ^ 2 ≤
      16 * (Real.sqrt r + Real.sqrt rho) *
        (Real.sqrt |r - rho|)⁻¹ := by
  have hsum : 0 ≤ r + rho := by linarith
  have hquot : 0 ≤ (r + rho) / |r - rho| :=
    div_nonneg hsum (abs_nonneg _)
  have hlog := Real.log_le_rpow_div hquot
    (show 0 < (1 / 4 : ℝ) by norm_num)
  have hlog_nonneg := hartreeRadialLog_nonneg r rho hr hrho
  have hquarter :
      hartreeRadialLog r rho ≤
        4 * ((r + rho) / |r - rho|) ^ (1 / 4 : ℝ) := by
    unfold hartreeRadialLog
    convert hlog using 1
    all_goals ring_nf
  have hsq :
      hartreeRadialLog r rho ^ 2 ≤
        16 * (((r + rho) / |r - rho|) ^ (1 / 4 : ℝ)) ^ 2 := by
    nlinarith [Real.rpow_nonneg hquot (1 / 4 : ℝ)]
  have hrpow :
      (((r + rho) / |r - rho|) ^ (1 / 4 : ℝ)) ^ 2 =
        Real.sqrt ((r + rho) / |r - rho|) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hquot]
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hsqrtadd : Real.sqrt (r + rho) ≤
      Real.sqrt r + Real.sqrt rho := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hr.le, Real.sq_sqrt hrho.le,
        mul_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg rho)]
  calc
    hartreeRadialLog r rho ^ 2 ≤
        16 * (((r + rho) / |r - rho|) ^ (1 / 4 : ℝ)) ^ 2 := hsq
    _ = 16 * (Real.sqrt (r + rho) / Real.sqrt |r - rho|) := by
      rw [hrpow, Real.sqrt_div hsum]
    _ ≤ 16 * ((Real.sqrt r + Real.sqrt rho) /
        Real.sqrt |r - rho|) := by gcongr
    _ = 16 * (Real.sqrt r + Real.sqrt rho) *
        (Real.sqrt |r - rho|)⁻¹ := by ring

/-- Integrable majorant for the near-diagonal part of the squared kernel. -/
def hartreeKernelSqNearMajorant (p : ℝ × ℝ) : ℝ :=
  kernelSquareSqrtWeight p.1 * kernelSquareWeight p.2 *
      diagonalSqrtKernel (p.1 - p.2) +
    kernelSquareWeight p.1 * kernelSquareSqrtWeight p.2 *
      diagonalSqrtKernel (p.1 - p.2)

/-- Integrable majorant away from the diagonal for the squared kernel. -/
def hartreeKernelSqFarMajorant (p : ℝ × ℝ) : ℝ :=
  kernelSquareSqrtWeight p.1 * kernelSquareWeight p.2 +
    kernelSquareWeight p.1 * kernelSquareSqrtWeight p.2

theorem hartreeKernelSqNearMajorant_nonneg (p : ℝ × ℝ) :
    0 ≤ hartreeKernelSqNearMajorant p := by
  unfold hartreeKernelSqNearMajorant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (kernelSquareSqrtWeight_nonneg _) (kernelSquareWeight_nonneg _))
      (diagonalSqrtKernel_nonneg _))
    (mul_nonneg
      (mul_nonneg (kernelSquareWeight_nonneg _) (kernelSquareSqrtWeight_nonneg _))
      (diagonalSqrtKernel_nonneg _))

theorem hartreeKernelSqFarMajorant_nonneg (p : ℝ × ℝ) :
    0 ≤ hartreeKernelSqFarMajorant p := by
  unfold hartreeKernelSqFarMajorant
  exact add_nonneg
    (mul_nonneg (kernelSquareSqrtWeight_nonneg _) (kernelSquareWeight_nonneg _))
    (mul_nonneg (kernelSquareWeight_nonneg _) (kernelSquareSqrtWeight_nonneg _))

theorem hartreeKernelSqNearMajorant_integrable :
    Integrable hartreeKernelSqNearMajorant (volume.prod volume) := by
  have hconv0 : Integrable
      (fun p : ℝ × ℝ => kernelSquareWeight p.2 *
        diagonalSqrtKernel (p.1 - p.2)) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      kernelSquareWeight_integrable.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ) diagonalSqrtKernel_integrable
  have hconv1 : Integrable
      (fun p : ℝ × ℝ => kernelSquareSqrtWeight p.2 *
        diagonalSqrtKernel (p.1 - p.2)) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      kernelSquareSqrtWeight_integrable.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ) diagonalSqrtKernel_integrable
  have hnear0 := hconv0.bdd_mul
    (kernelSquareSqrtWeight_continuous.comp continuous_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p : ℝ × ℝ =>
      kernelSquareSqrtWeight_norm_le_one p.1)
  have hnear1 := hconv1.bdd_mul
    (kernelSquareWeight_continuous.comp continuous_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p : ℝ × ℝ =>
      kernelSquareWeight_norm_le_one p.1)
  change Integrable (fun p : ℝ × ℝ =>
    kernelSquareSqrtWeight p.1 * kernelSquareWeight p.2 *
        diagonalSqrtKernel (p.1 - p.2) +
      kernelSquareWeight p.1 * kernelSquareSqrtWeight p.2 *
        diagonalSqrtKernel (p.1 - p.2)) (volume.prod volume)
  refine (hnear0.add hnear1).congr ?_
  filter_upwards with p
  simp only [Function.comp_apply, Pi.add_apply]
  ring

theorem hartreeKernelSqFarMajorant_integrable :
    Integrable hartreeKernelSqFarMajorant (volume.prod volume) := by
  have h0 := kernelSquareSqrtWeight_integrable.mul_prod
    kernelSquareWeight_integrable
  have h1 := kernelSquareWeight_integrable.mul_prod
    kernelSquareSqrtWeight_integrable
  exact h0.add h1

/-- Global integrable majorant for the square of the Hartree kernel. -/
def hartreeKernelSqMajorant (p : ℝ × ℝ) : ℝ :=
  16 * |8 * Real.pi * hartreeKappa| ^ 2 *
    (hartreeKernelSqNearMajorant p + hartreeKernelSqFarMajorant p)

theorem hartreeKernelSqMajorant_nonneg (p : ℝ × ℝ) :
    0 ≤ hartreeKernelSqMajorant p := by
  unfold hartreeKernelSqMajorant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (add_nonneg (hartreeKernelSqNearMajorant_nonneg p)
      (hartreeKernelSqFarMajorant_nonneg p))

theorem hartreeKernelSqMajorant_integrable :
    Integrable hartreeKernelSqMajorant (volume.prod volume) := by
  exact (hartreeKernelSqNearMajorant_integrable.add
    hartreeKernelSqFarMajorant_integrable).const_mul
      (16 * |8 * Real.pi * hartreeKappa| ^ 2)

theorem hartreeKernel_norm_sq_eq
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho) :
    ‖hartreeKernel r rho‖ ^ 2 =
      |8 * Real.pi * hartreeKappa| ^ 2 *
        kernelSquareWeight r * kernelSquareWeight rho *
          hartreeRadialLog r rho ^ 2 := by
  have hlog := hartreeRadialLog_nonneg r rho hr hrho
  have hbr : |bubble r| = bubble r :=
    abs_of_nonneg (by unfold bubble; positivity)
  have hbrho : |bubble rho| = bubble rho :=
    abs_of_nonneg (by unfold bubble; positivity)
  have hl : |Real.log ((r + rho) / |r - rho|)| =
      Real.log ((r + rho) / |r - rho|) := by
    apply abs_of_nonneg
    simpa [hartreeRadialLog] using hlog
  rw [Real.norm_eq_abs]
  unfold hartreeKernel kernelSquareWeight hartreeRadialLog
  simp only [abs_mul, abs_pow, hbr, hbrho, hl]
  ring

theorem hartreeKernel_norm_sq_le_majorant
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho) :
    ‖hartreeKernel r rho‖ ^ 2 ≤ hartreeKernelSqMajorant (r, rho) := by
  rw [hartreeKernel_norm_sq_eq r rho hr hrho]
  have hlog := hartreeRadialLog_sq_sqrt_bound r rho hr hrho
  have hfac : 0 ≤ |8 * Real.pi * hartreeKappa| ^ 2 *
      kernelSquareWeight r * kernelSquareWeight rho := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (kernelSquareWeight_nonneg r))
      (kernelSquareWeight_nonneg rho)
  by_cases hnear : |r - rho| < 1
  · have hdiag : diagonalSqrtKernel (r - rho) =
        (Real.sqrt |r - rho|)⁻¹ := by
      simp [diagonalSqrtKernel, hnear]
    calc
      |8 * Real.pi * hartreeKappa| ^ 2 * kernelSquareWeight r *
          kernelSquareWeight rho * hartreeRadialLog r rho ^ 2 ≤
          (|8 * Real.pi * hartreeKappa| ^ 2 * kernelSquareWeight r *
            kernelSquareWeight rho) *
            (16 * (Real.sqrt r + Real.sqrt rho) *
              (Real.sqrt |r - rho|)⁻¹) :=
        mul_le_mul_of_nonneg_left hlog hfac
      _ = 16 * |8 * Real.pi * hartreeKappa| ^ 2 *
          hartreeKernelSqNearMajorant (r, rho) := by
        unfold hartreeKernelSqNearMajorant kernelSquareSqrtWeight
        rw [hdiag]
        ring
      _ ≤ hartreeKernelSqMajorant (r, rho) := by
        unfold hartreeKernelSqMajorant
        gcongr
        exact le_add_of_nonneg_right
          (hartreeKernelSqFarMajorant_nonneg (r, rho))
  · have hfar : 1 ≤ |r - rho| := le_of_not_gt hnear
    have hsqrt : 1 ≤ Real.sqrt |r - rho| := by
      have h := Real.sqrt_le_sqrt hfar
      simpa using h
    have hinv : (Real.sqrt |r - rho|)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity : 0 < Real.sqrt |r - rho|)).2 hsqrt
    have hlogfar : hartreeRadialLog r rho ^ 2 ≤
        16 * (Real.sqrt r + Real.sqrt rho) := by
      calc
        hartreeRadialLog r rho ^ 2 ≤
            16 * (Real.sqrt r + Real.sqrt rho) *
              (Real.sqrt |r - rho|)⁻¹ := hlog
        _ ≤ 16 * (Real.sqrt r + Real.sqrt rho) := by
          nlinarith [Real.sqrt_nonneg r, Real.sqrt_nonneg rho]
    calc
      |8 * Real.pi * hartreeKappa| ^ 2 * kernelSquareWeight r *
          kernelSquareWeight rho * hartreeRadialLog r rho ^ 2 ≤
          (|8 * Real.pi * hartreeKappa| ^ 2 * kernelSquareWeight r *
            kernelSquareWeight rho) *
            (16 * (Real.sqrt r + Real.sqrt rho)) :=
        mul_le_mul_of_nonneg_left hlogfar hfac
      _ = 16 * |8 * Real.pi * hartreeKappa| ^ 2 *
          hartreeKernelSqFarMajorant (r, rho) := by
        unfold hartreeKernelSqFarMajorant kernelSquareSqrtWeight
        ring
      _ ≤ hartreeKernelSqMajorant (r, rho) := by
        unfold hartreeKernelSqMajorant
        gcongr
        exact le_add_of_nonneg_left
          (hartreeKernelSqNearMajorant_nonneg (r, rho))

/-- The radial Hartree kernel is genuinely square integrable on the positive
quadrant. -/
theorem hartreeKernel_sq_integrable :
    Integrable (fun p : ℝ × ℝ => hartreeKernel p.1 p.2 ^ 2)
      (halfLineMeasure.prod halfLineMeasure) := by
  rw [Measure.prod_restrict]
  have hmajor : IntegrableOn hartreeKernelSqMajorant
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (volume.prod volume) :=
    hartreeKernelSqMajorant_integrable.integrableOn
  refine hmajor.mono'
    ((hartreeKernel_uncurry_measurable.pow_const 2).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := hartreeKernel_norm_sq_le_majorant p.1 p.2 hp.1 hp.2
  rw [Real.norm_eq_abs, sq_abs] at h
  simpa only using h

theorem hartreeKernel_memLp_two :
    MemLp (Function.uncurry hartreeKernel) 2
      (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq
    hartreeKernel_uncurry_measurable.aestronglyMeasurable).2
  exact hartreeKernel_sq_integrable

/-- Product-L2 vector represented by the actual Hartree kernel. -/
def hartreeKernelL2 :
    HBL.L2Kernel.RealKernelL2 halfLineMeasure :=
  hartreeKernel_memLp_two.toLp (Function.uncurry hartreeKernel)

theorem hartreeKernelL2_ae :
    (hartreeKernelL2 : ℝ × ℝ → ℝ) =ᵐ[
      halfLineMeasure.prod halfLineMeasure]
      Function.uncurry hartreeKernel :=
  hartreeKernel_memLp_two.coeFn_toLp

/-- The actual bounded L2 integral operator supplied by the radial kernel. -/
def hartreeKernelOperator :
    HBL.L2Kernel.RealL2 halfLineMeasure →L[ℝ]
      HBL.L2Kernel.RealL2 halfLineMeasure :=
  HBL.L2Kernel.operator hartreeKernelL2

theorem hartreeKernelOperator_hilbertSchmidt :
    HBL.L2Kernel.IsHilbertSchmidtKernelOperator
      hartreeKernelOperator hartreeKernelL2 :=
  HBL.L2Kernel.operator_isHilbertSchmidtKernelOperator hartreeKernelL2

/-- Weak integral action of the constructed operator, written with the
actual radial kernel rather than its L2 equivalence class. -/
theorem hartreeKernelOperator_weak_apply
    (f g : HBL.L2Kernel.RealL2 halfLineMeasure) :
    inner ℝ (hartreeKernelOperator f) g =
      ∫ p : ℝ × ℝ,
        hartreeKernel p.1 p.2 * (g p.1 * f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
  change inner ℝ (HBL.L2Kernel.operator hartreeKernelL2 f) g = _
  rw [HBL.L2Kernel.inner_operator, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hartreeKernelL2_ae,
    HBL.L2Kernel.tensor_ae g f] with p hK ht
  rw [hK, ht]
  rw [Real.inner_apply]
  change hartreeKernel p.1 p.2 * (g p.1 * f p.2) = _
  rfl

theorem hartreeKernel_inner_tensor_swap
    (f g : HBL.L2Kernel.RealL2 halfLineMeasure) :
    inner ℝ hartreeKernelL2 (HBL.L2Kernel.tensor g f) =
      inner ℝ hartreeKernelL2 (HBL.L2Kernel.tensor f g) := by
  rw [L2.inner_def, L2.inner_def]
  have hleft :
      (fun p : ℝ × ℝ => inner ℝ (hartreeKernelL2 p)
        (HBL.L2Kernel.tensor g f p)) =ᵐ[
          halfLineMeasure.prod halfLineMeasure]
      fun p => hartreeKernel p.1 p.2 * (g p.1 * f p.2) := by
    filter_upwards [hartreeKernelL2_ae,
      HBL.L2Kernel.tensor_ae g f] with p hK ht
    rw [hK, ht]
    rw [Real.inner_apply]
    change hartreeKernel p.1 p.2 * (g p.1 * f p.2) = _
    rfl
  have hright :
      (fun p : ℝ × ℝ => inner ℝ (hartreeKernelL2 p)
        (HBL.L2Kernel.tensor f g p)) =ᵐ[
          halfLineMeasure.prod halfLineMeasure]
      fun p => hartreeKernel p.1 p.2 * (f p.1 * g p.2) := by
    filter_upwards [hartreeKernelL2_ae,
      HBL.L2Kernel.tensor_ae f g] with p hK ht
    rw [hK, ht]
    rw [Real.inner_apply]
    change hartreeKernel p.1 p.2 * (f p.1 * g p.2) = _
    rfl
  rw [integral_congr_ae hleft, integral_congr_ae hright]
  calc
    (∫ p : ℝ × ℝ, hartreeKernel p.1 p.2 * (g p.1 * f p.2)
        ∂(halfLineMeasure.prod halfLineMeasure)) =
        ∫ p : ℝ × ℝ,
          (fun q : ℝ × ℝ =>
            hartreeKernel q.1 q.2 * (g q.1 * f q.2)) p.swap
          ∂(halfLineMeasure.prod halfLineMeasure) := by
      symm
      simpa only using (MeasureTheory.integral_prod_swap
        (μ := halfLineMeasure) (ν := halfLineMeasure)
        (fun q : ℝ × ℝ =>
          hartreeKernel q.1 q.2 * (g q.1 * f q.2)))
    _ = ∫ p : ℝ × ℝ,
        hartreeKernel p.1 p.2 * (f p.1 * g p.2)
        ∂(halfLineMeasure.prod halfLineMeasure) := by
      apply integral_congr_ae
      filter_upwards with p
      change hartreeKernel p.2 p.1 * (g p.2 * f p.1) =
        hartreeKernel p.1 p.2 * (f p.1 * g p.2)
      rw [hartreeKernel_symm]
      ring

/-- Symmetry of the kernel upgrades the actual L2 realization to a
self-adjoint operator. -/
theorem hartreeKernelOperator_selfAdjoint :
    IsSelfAdjoint hartreeKernelOperator := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  calc
    inner ℝ (hartreeKernelOperator f) g =
        inner ℝ hartreeKernelL2 (HBL.L2Kernel.tensor g f) :=
      HBL.L2Kernel.inner_operator _ _ _
    _ = inner ℝ hartreeKernelL2 (HBL.L2Kernel.tensor f g) :=
      hartreeKernel_inner_tensor_swap f g
    _ = inner ℝ (hartreeKernelOperator g) f :=
      (HBL.L2Kernel.inner_operator _ _ _).symm
    _ = inner ℝ f (hartreeKernelOperator g) := real_inner_comm _ _

/-- The Japanese bracket used in the two pointwise kernel estimates. -/
def kernelBracket (r : ℝ) : ℝ := Real.sqrt (1 + r ^ 2)

theorem kernelBracket_pos (r : ℝ) : 0 < kernelBracket r := by
  unfold kernelBracket
  positivity

theorem bubble_pow_three_le_inv_pow_three
    (r : ℝ) (hr : 0 < r) :
    bubble r ^ 3 ≤ r⁻¹ ^ 3 := by
  have hsge : r ≤ Real.sqrt (1 + r ^ 2) := by
    calc
      r = Real.sqrt (r ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]
      _ ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hinv : (Real.sqrt (1 + r ^ 2))⁻¹ ≤ r⁻¹ :=
    (inv_le_inv₀ (by positivity : 0 < Real.sqrt (1 + r ^ 2)) hr).2 hsge
  unfold bubble
  exact pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hinv 3

theorem bubble_pow_three_eq_bracket (r : ℝ) :
    bubble r ^ 3 = (kernelBracket r)⁻¹ ^ 3 := by
  rfl

theorem hartreeKernel_abs_eq
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho) :
    |hartreeKernel r rho| =
      |8 * Real.pi * hartreeKappa| * bubble r ^ 3 * bubble rho ^ 3 *
        hartreeRadialLog r rho := by
  have hbr : 0 ≤ bubble r := by unfold bubble; positivity
  have hbrho : 0 ≤ bubble rho := by unfold bubble; positivity
  have hlog := hartreeRadialLog_nonneg r rho hr hrho
  change
    |8 * Real.pi * hartreeKappa * bubble r ^ 3 * bubble rho ^ 3 *
        hartreeRadialLog r rho| = _
  simp only [abs_mul, abs_pow, abs_of_nonneg hbr, abs_of_nonneg hbrho,
    abs_of_nonneg hlog]

/-- Logarithmic estimate in the separated ordered region `2 rho ≤ r`. -/
theorem hartreeRadialLog_separated_ordered
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hsep : 2 * rho ≤ r) :
    hartreeRadialLog r rho ≤ 4 * rho / r := by
  have hdiff : 0 < r - rho := by linarith
  have hratio : 0 < (r + rho) / (r - rho) :=
    div_pos (by linarith) hdiff
  have hfirst := Real.log_le_sub_one_of_pos hratio
  have hfrac : 2 * rho / (r - rho) ≤ 4 * rho / r := by
    rw [div_le_div_iff₀ hdiff hr]
    nlinarith [mul_nonneg hrho.le (sub_nonneg.mpr hsep)]
  unfold hartreeRadialLog
  rw [abs_of_pos hdiff]
  calc
    Real.log ((r + rho) / (r - rho)) ≤
        (r + rho) / (r - rho) - 1 := hfirst
    _ = 2 * rho / (r - rho) := by field_simp; ring
    _ ≤ 4 * rho / r := hfrac

/-- Separated-region estimate with the larger radius in the first slot. -/
theorem hartreeKernel_separated_ordered
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hsep : 2 * rho ≤ r) :
    |hartreeKernel r rho| ≤
      (4 * |8 * Real.pi * hartreeKappa|) * r⁻¹ ^ 4 * rho *
        (kernelBracket rho)⁻¹ ^ 3 := by
  rw [hartreeKernel_abs_eq r rho hr hrho,
    bubble_pow_three_eq_bracket]
  have hb := bubble_pow_three_le_inv_pow_three r hr
  have hlog := hartreeRadialLog_separated_ordered r rho hr hrho hsep
  have hlog0 := hartreeRadialLog_nonneg r rho hr hrho
  have hC : 0 ≤ |8 * Real.pi * hartreeKappa| := abs_nonneg _
  have hbrho : 0 ≤ (kernelBracket rho)⁻¹ ^ 3 :=
    pow_nonneg (inv_nonneg.mpr (kernelBracket_pos rho).le) _
  have hloginv : 0 ≤ 4 * rho / r := by positivity
  calc
    |8 * Real.pi * hartreeKappa| * bubble r ^ 3 *
        (kernelBracket rho)⁻¹ ^ 3 * hartreeRadialLog r rho ≤
        |8 * Real.pi * hartreeKappa| * r⁻¹ ^ 3 *
          (kernelBracket rho)⁻¹ ^ 3 * (4 * rho / r) := by
      gcongr
    _ = (4 * |8 * Real.pi * hartreeKappa|) * r⁻¹ ^ 4 * rho *
        (kernelBracket rho)⁻¹ ^ 3 := by
      field_simp [ne_of_gt hr]

/-- Symmetric separated-region estimate in the manuscript's `M,m`
notation. -/
theorem hartreeKernel_separated
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hsep : 2 * min r rho ≤ max r rho) :
    |hartreeKernel r rho| ≤
      (4 * |8 * Real.pi * hartreeKappa|) * (max r rho)⁻¹ ^ 4 *
        min r rho * (kernelBracket (min r rho))⁻¹ ^ 3 := by
  by_cases h : r ≤ rho
  · have hs : 2 * r ≤ rho := by simpa [min_eq_left h, max_eq_right h] using hsep
    rw [hartreeKernel_symm]
    simpa [min_eq_left h, max_eq_right h] using
      hartreeKernel_separated_ordered rho r hrho hr hs
  · have h' : rho ≤ r := le_of_not_ge h
    have hs : 2 * rho ≤ r := by simpa [min_eq_right h', max_eq_left h'] using hsep
    simpa [min_eq_right h', max_eq_left h'] using
      hartreeKernel_separated_ordered r rho hr hrho hs

/-- Logarithmic bound in the ordered near-diagonal region.  The statement
also covers the diagonal, where the totalized kernel value is zero. -/
theorem hartreeRadialLog_diagonal_ordered
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho) (hle : rho ≤ r) :
    hartreeRadialLog r rho ≤
      1 + |Real.log (|r - rho| / r)| := by
  by_cases heq : r = rho
  · subst rho
    simp [hartreeRadialLog]
  · have hlt : rho < r := lt_of_le_of_ne hle (Ne.symm heq)
    have hdiff : 0 < r - rho := sub_pos.mpr hlt
    have hxpos : 0 < (r - rho) / r := div_pos hdiff hr
    have hxle : (r - rho) / r ≤ 1 := by
      rw [div_le_one hr]
      linarith
    have hratio : (r + rho) / (r - rho) ≤
        2 / ((r - rho) / r) := by
      rw [div_le_div_iff₀ hdiff hxpos]
      field_simp [ne_of_gt hr]
      nlinarith [mul_pos hr hdiff]
    have hratioPos : 0 < (r + rho) / (r - rho) :=
      div_pos (by linarith) hdiff
    have hlogmono := Real.log_le_log hratioPos hratio
    have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hlogx : Real.log ((r - rho) / r) ≤ 0 :=
      Real.log_nonpos hxpos.le hxle
    have habs : |Real.log ((r - rho) / r)| =
        -Real.log ((r - rho) / r) := abs_of_nonpos hlogx
    unfold hartreeRadialLog
    rw [abs_of_pos hdiff]
    calc
      Real.log ((r + rho) / (r - rho)) ≤
          Real.log (2 / ((r - rho) / r)) := hlogmono
      _ = Real.log 2 - Real.log ((r - rho) / r) := by
        rw [Real.log_div (by norm_num) (ne_of_gt hxpos)]
      _ ≤ 1 + |Real.log ((r - rho) / r)| := by
        rw [habs]
        linarith

/-- Comparison of the two bubble factors in the ordered near-diagonal
region. -/
theorem bubble_pow_three_near_ordered
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hnear : r ≤ 2 * rho) :
    bubble rho ^ 3 ≤ 8 * (kernelBracket r)⁻¹ ^ 3 := by
  have hr2 : r ^ 2 ≤ (2 * rho) ^ 2 :=
    (sq_le_sq₀ hr.le (by positivity)).2 hnear
  have hsR2 : kernelBracket r ^ 2 = 1 + r ^ 2 := by
    unfold kernelBracket
    exact Real.sq_sqrt (by positivity)
  have hsM2 : kernelBracket rho ^ 2 = 1 + rho ^ 2 := by
    unfold kernelBracket
    exact Real.sq_sqrt (by positivity)
  have hbase : 1 + r ^ 2 ≤ 4 * (1 + rho ^ 2) := by nlinarith
  have hscomp : kernelBracket r ≤ 2 * kernelBracket rho := by
    nlinarith [kernelBracket_pos r, kernelBracket_pos rho]
  have hinv : (kernelBracket rho)⁻¹ ≤ 2 * (kernelBracket r)⁻¹ := by
    rw [show 2 * (kernelBracket r)⁻¹ = 2 / kernelBracket r by ring]
    rw [le_div_iff₀ (kernelBracket_pos r)]
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ (kernelBracket_pos rho)).2 hscomp
  rw [bubble_pow_three_eq_bracket]
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr (kernelBracket_pos rho).le) hinv 3
  calc
    (kernelBracket rho)⁻¹ ^ 3 ≤
        (2 * (kernelBracket r)⁻¹) ^ 3 := hp
    _ = 8 * (kernelBracket r)⁻¹ ^ 3 := by ring

/-- Near-diagonal estimate with the larger radius in the first slot. -/
theorem hartreeKernel_diagonal_ordered
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hle : rho ≤ r) (hnear : r ≤ 2 * rho) :
    |hartreeKernel r rho| ≤
      (8 * |8 * Real.pi * hartreeKappa|) *
        (kernelBracket r)⁻¹ ^ 6 *
          (1 + |Real.log (|r - rho| / r)|) := by
  rw [hartreeKernel_abs_eq r rho hr hrho,
    bubble_pow_three_eq_bracket]
  have hb := bubble_pow_three_near_ordered r rho hr hrho hnear
  have hlog := hartreeRadialLog_diagonal_ordered r rho hr hrho hle
  have hlog0 := hartreeRadialLog_nonneg r rho hr hrho
  have hC : 0 ≤ |8 * Real.pi * hartreeKappa| := abs_nonneg _
  have hbr : 0 ≤ (kernelBracket r)⁻¹ ^ 3 :=
    pow_nonneg (inv_nonneg.mpr (kernelBracket_pos r).le) _
  have htail : 0 ≤ 1 + |Real.log (|r - rho| / r)| := by positivity
  calc
    |8 * Real.pi * hartreeKappa| * (kernelBracket r)⁻¹ ^ 3 *
        bubble rho ^ 3 * hartreeRadialLog r rho ≤
        |8 * Real.pi * hartreeKappa| * (kernelBracket r)⁻¹ ^ 3 *
          (8 * (kernelBracket r)⁻¹ ^ 3) *
            (1 + |Real.log (|r - rho| / r)|) := by
      gcongr
    _ = (8 * |8 * Real.pi * hartreeKappa|) *
        (kernelBracket r)⁻¹ ^ 6 *
          (1 + |Real.log (|r - rho| / r)|) := by ring

/-- Symmetric near-diagonal estimate in the manuscript's `M,m` notation. -/
theorem hartreeKernel_diagonal
    (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hnear : max r rho ≤ 2 * min r rho) :
    |hartreeKernel r rho| ≤
      (8 * |8 * Real.pi * hartreeKappa|) *
        (kernelBracket (max r rho))⁻¹ ^ 6 *
          (1 + |Real.log (|r - rho| / max r rho)|) := by
  by_cases h : r ≤ rho
  · have hn : rho ≤ 2 * r := by
      simpa [min_eq_left h, max_eq_right h] using hnear
    rw [hartreeKernel_symm]
    simpa [min_eq_left h, max_eq_right h, abs_sub_comm] using
      hartreeKernel_diagonal_ordered rho r hrho hr h hn
  · have h' : rho ≤ r := le_of_not_ge h
    have hn : r ≤ 2 * rho := by
      simpa [min_eq_right h', max_eq_left h'] using hnear
    simpa [min_eq_right h', max_eq_left h'] using
      hartreeKernel_diagonal_ordered r rho hr hrho h' hn

/-- Terminal theorem matching the complete numbered manuscript environment
`lem:kernel-short`.  It records the symmetric product-L2 kernel, its actual
bounded weak integral realization, the Hilbert--Schmidt kernel certificate,
self-adjointness, and the two pointwise regions with one common constant. -/
theorem kernelShortManuscriptEnvironment_closed :
    (∀ r rho : ℝ, hartreeKernel r rho = hartreeKernel rho r) ∧
    MemLp (fun p : ℝ × ℝ => hartreeKernel p.1 p.2) 2
      (halfLineMeasure.prod halfLineMeasure) ∧
    HBL.L2Kernel.IsHilbertSchmidtKernelOperator
      hartreeKernelOperator hartreeKernelL2 ∧
    IsSelfAdjoint hartreeKernelOperator ∧
    (∀ f g : HBL.L2Kernel.RealL2 halfLineMeasure,
      inner ℝ (hartreeKernelOperator f) g =
        ∫ p : ℝ × ℝ,
          hartreeKernel p.1 p.2 * (g p.1 * f p.2)
          ∂(halfLineMeasure.prod halfLineMeasure)) ∧
    ∃ C : ℝ, 0 < C ∧
      (∀ r rho : ℝ, 0 < r → 0 < rho →
        2 * min r rho ≤ max r rho →
        |hartreeKernel r rho| ≤
          C * (max r rho)⁻¹ ^ 4 * min r rho *
            (kernelBracket (min r rho))⁻¹ ^ 3) ∧
      (∀ r rho : ℝ, 0 < r → 0 < rho →
        max r rho ≤ 2 * min r rho →
        |hartreeKernel r rho| ≤
          C * (kernelBracket (max r rho))⁻¹ ^ 6 *
            (1 + |Real.log (|r - rho| / max r rho)|)) := by
  refine ⟨hartreeKernel_symm, hartreeKernel_memLp_two,
    hartreeKernelOperator_hilbertSchmidt,
    hartreeKernelOperator_selfAdjoint,
    hartreeKernelOperator_weak_apply, ?_⟩
  let C : ℝ := 8 * |8 * Real.pi * hartreeKappa|
  have hbase : 0 < 8 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num) (abs_pos.mpr (ne_of_gt hbase))
  refine ⟨C, hC, ?_, ?_⟩
  · intro r rho hr hrho hsep
    have h := hartreeKernel_separated r rho hr hrho hsep
    have hmin : 0 < min r rho := lt_min hr hrho
    have hmax : 0 < max r rho := lt_max_of_lt_left hr
    have htail : 0 ≤
        (max r rho)⁻¹ ^ 4 * min r rho *
          (kernelBracket (min r rho))⁻¹ ^ 3 := by
      exact mul_nonneg
        (mul_nonneg
          (pow_nonneg (inv_nonneg.mpr hmax.le) _)
          hmin.le)
        (pow_nonneg
          (inv_nonneg.mpr (kernelBracket_pos (min r rho)).le) _)
    have hcoef :
        4 * |8 * Real.pi * hartreeKappa| ≤
          8 * |8 * Real.pi * hartreeKappa| := by
      nlinarith [abs_nonneg (8 * Real.pi * hartreeKappa)]
    calc
      |hartreeKernel r rho| ≤
          (4 * |8 * Real.pi * hartreeKappa|) *
            (max r rho)⁻¹ ^ 4 * min r rho *
              (kernelBracket (min r rho))⁻¹ ^ 3 := h
      _ = (4 * |8 * Real.pi * hartreeKappa|) *
            ((max r rho)⁻¹ ^ 4 * min r rho *
              (kernelBracket (min r rho))⁻¹ ^ 3) := by ring
      _ ≤ (8 * |8 * Real.pi * hartreeKappa|) *
            ((max r rho)⁻¹ ^ 4 * min r rho *
              (kernelBracket (min r rho))⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_right hcoef htail
      _ ≤ C * (max r rho)⁻¹ ^ 4 * min r rho *
            (kernelBracket (min r rho))⁻¹ ^ 3 := by
        dsimp [C]
        ring_nf
        exact le_rfl
  · intro r rho hr hrho hnear
    exact hartreeKernel_diagonal r rho hr hrho hnear

end HBL.Modulation.AffineTail
