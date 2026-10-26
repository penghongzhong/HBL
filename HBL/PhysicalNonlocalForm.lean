import HBL.PhysicalPhaseHessian
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Group.Prod

/-!
R18: actual three-dimensional nonlocal Hartree bilinear integral on every
constructed energy state. Cubic bubble densities are derived to be L1 and L2.
Near the diagonal use the locally L1 inverse-square kernel and translated
square majorants; in the far field use the L1 density. No HLS or angular
reduction assumption is added. The radial logarithmic identity remains open.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail
private abbrev X := PhysicalRadialSpace3
private abbrev E := PhysicalRadialEnergyCompletion
private abbrev μ : Measure X := volume
private abbrev μ₂ : Measure (X × X) := μ.prod μ

private theorem ae_fst {f g : X → ℝ} (h : f =ᵐ[μ] g) :
    (fun p : X × X => f p.1) =ᵐ[μ₂] (fun p => g p.1) :=
  h.comp_tendsto (show QuasiMeasurePreserving Prod.fst μ₂ μ from quasiMeasurePreserving_fst).tendsto_ae
private theorem ae_snd {f g : X → ℝ} (h : f =ᵐ[μ] g) :
    (fun p : X × X => f p.2) =ᵐ[μ₂] (fun p => g p.2) :=
  h.comp_tendsto (show QuasiMeasurePreserving Prod.snd μ₂ μ from quasiMeasurePreserving_snd).tendsto_ae

local instance : Fact ((1 : ENNReal) ≤ 3) := ⟨by norm_num⟩
local instance : Fact ((1 : ENNReal) ≤ 6) := ⟨by norm_num⟩
local instance : ENNReal.HolderTriple 3 6 2 where
  inv_add_inv_eq_inv := by
    change ((3 : ℝ≥0) : ENNReal)⁻¹ + ((6 : ℝ≥0) : ENNReal)⁻¹ = ((2 : ℝ≥0) : ENNReal)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (3 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
    norm_num
local instance : ENNReal.HolderConjugate (6 / 5) 6 where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (by simp) (by simp)]
    change ((5 : ℝ≥0) : ENNReal) / ((6 : ℝ≥0) : ENNReal) +
      ((6 : ℝ≥0) : ENNReal)⁻¹ = 1⁻¹
    rw [← ENNReal.coe_div (by norm_num : (6 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
    norm_num

local instance : Fact ((1 : ENNReal) ≤ 6 / 5) :=
  ⟨ENNReal.HolderConjugate.one_le (6 / 5) 6⟩

/-- The genuine cubic bubble density weight on physical Euclidean space. -/
def physicalCubicWeight (x : PhysicalRadialSpace3) : ℝ := bubble ‖x‖ ^ 3
private theorem cubicWeight_rpow (x : X) :
    physicalCubicWeight x = (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) := by
  unfold physicalCubicWeight bubble
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow,
    Real.inv_rpow (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_neg (by positivity)]
  congr 1
  norm_num
private theorem cubicWeight_mem (p : ENNReal) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hp : 1 < p.toReal) : MemLp physicalCubicWeight p μ := by
  have hm : AEStronglyMeasurable physicalCubicWeight μ :=
    ((bubble_contDiff.continuous.comp continuous_norm).pow 3).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm hp0 hpt).mp
  have hi : Integrable (fun x : X => (1 + ‖x‖ ^ 2) ^ (-(3 * p.toReal) / 2)) μ :=
    integrable_rpow_neg_one_add_norm_sq (by
      have hd : Module.finrank ℝ X = 3 := by simp [X, PhysicalRadialSpace3]
      rw [hd]
      norm_num
      linarith)
  apply hi.congr
  filter_upwards with x
  rw [cubicWeight_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (by positivity)]
  congr 1
  ring
private def cubicL3 : Lp ℝ 3 μ :=
  (cubicWeight_mem 3 (by norm_num) (by norm_num) (by norm_num)).toLp physicalCubicWeight
private def cubicL65 : Lp ℝ (6 / 5) μ :=
  (cubicWeight_mem (6 / 5) (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)).toLp physicalCubicWeight

/-- The actual density as a bounded L2-valued map. -/
def physicalHartreeDensityL2 : E →L[ℝ] PhysicalScalarL2 :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL μ 3 6 2 cubicL3).comp physicalL6Realization
/-- The SAME actual density as a bounded L1-valued map. -/
def physicalHartreeDensityL1 : E →L[ℝ] Lp ℝ 1 μ :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL μ (6 / 5) 6 1 cubicL65).comp physicalL6Realization
private theorem density2_ae (u : E) :
    (physicalHartreeDensityL2 u : X → ℝ) =ᵐ[μ]
      (fun x => physicalCubicWeight x * physicalL6Realization u x) := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := (2 : ENNReal)) cubicL3 (physicalL6Realization u)
  filter_upwards [h, (cubicWeight_mem 3 (by norm_num) (by norm_num) (by norm_num)).coeFn_toLp]
    with x hx hw
  change physicalHartreeDensityL2 u x = cubicL3 x * physicalL6Realization u x at hx
  rw [hx]
  exact congrArg (fun a => a * physicalL6Realization u x) hw
private theorem density1_ae (u : E) :
    (physicalHartreeDensityL1 u : X → ℝ) =ᵐ[μ]
      (fun x => physicalCubicWeight x * physicalL6Realization u x) := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := (1 : ENNReal)) cubicL65 (physicalL6Realization u)
  filter_upwards [h,
    (cubicWeight_mem (6 / 5) (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)).coeFn_toLp]
    with x hx hw
  change physicalHartreeDensityL1 u x = cubicL65 x * physicalL6Realization u x at hx
  rw [hx]
  exact congrArg (fun a => a * physicalL6Realization u x) hw
private theorem density_integrable (u : E) : Integrable (physicalHartreeDensityL2 u) μ :=
  (memLp_one_iff_integrable.mp (Lp.memLp (physicalHartreeDensityL1 u))).congr
    ((density1_ae u).trans (density2_ae u).symm)
private theorem density_norm_integral (u : E) :
    (∫ x, ‖physicalHartreeDensityL2 u x‖ ∂μ) = ‖physicalHartreeDensityL1 u‖ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (((density2_ae u).trans (density1_ae u).symm).fun_comp norm)
private theorem density_sq_integral (u : E) :
    (∫ x, (physicalHartreeDensityL2 u x) ^ 2 ∂μ) = ‖physicalHartreeDensityL2 u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.inner_apply]
  ring

/-- Inverse-square kernel, with zero value on its null singular diagonal. -/
def physicalHartreeKernel (x : PhysicalRadialSpace3) : ℝ := (‖x‖ ^ 2)⁻¹
private def nearKernel (x : X) : ℝ := (ball (0 : X) 1).indicator physicalHartreeKernel x
private theorem kernel_meas : Measurable physicalHartreeKernel := by
  unfold physicalHartreeKernel
  fun_prop
private theorem near_meas : Measurable nearKernel := kernel_meas.indicator measurableSet_ball
private theorem near_nonneg (x : X) : 0 ≤ nearKernel x := by
  exact indicator_nonneg (fun _ _ => inv_nonneg.mpr (sq_nonneg _)) _
private theorem near_even (x : X) : nearKernel (-x) = nearKernel x := by
  simp [nearKernel, physicalHartreeKernel, Set.indicator]
private theorem near_integrable : Integrable nearKernel μ := by
  apply (integrable_indicator_iff measurableSet_ball).mpr
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2)
    (by norm_num [X, PhysicalRadialSpace3]) (by norm_num [X, PhysicalRadialSpace3])
  · filter_upwards with x
    simp only [physicalHartreeKernel, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (‖x‖ ^ 2)⁻¹), one_mul]
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
  · exact kernel_meas.aestronglyMeasurable
private theorem kernel_le_near_add_one (x : X) : physicalHartreeKernel x ≤ nearKernel x + 1 := by
  by_cases hx : x ∈ ball (0 : X) 1
  · simp only [nearKernel, indicator_of_mem hx]
    linarith
  · have hn : 1 ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    have hs : 1 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hi : (‖x‖ ^ 2)⁻¹ ≤ (1 : ℝ) := by
      simpa only [one_div, inv_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs)
    simpa only [nearKernel, indicator_of_notMem hx, zero_add, physicalHartreeKernel] using hi

private theorem near_square (u : E) :
    Integrable (fun p : X × X => nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.1) ^ 2) μ₂ ∧
    (∫ p : X × X, nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.1) ^ 2 ∂μ₂) =
      (∫ x, nearKernel x ∂μ) * ‖physicalHartreeDensityL2 u‖ ^ 2 := by
  have hs := (Lp.memLp (physicalHartreeDensityL2 u)).integrable_sq
  have hp := hs.mul_prod near_integrable
  have mp := measurePreserving_prod_sub μ μ
  have hi := (mp.integrable_comp hp.aestronglyMeasurable).mpr hp
  have he := mp.integral_comp (MeasurableEquiv.shearSubRight X).measurableEmbedding
    (fun p : X × X => (physicalHartreeDensityL2 u p.1) ^ 2 * nearKernel p.2)
  constructor
  · simpa only [Function.comp_def, mul_comm] using hi
  · calc
      (∫ p : X × X, nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.1) ^ 2 ∂μ₂) =
          ∫ p : X × X, (physicalHartreeDensityL2 u p.1) ^ 2 * nearKernel p.2 ∂μ₂ := by
            simpa only [mul_comm] using he
      _ = (∫ x, (physicalHartreeDensityL2 u x) ^ 2 ∂μ) * (∫ y, nearKernel y ∂μ) := by
        rw [integral_prod _ hp]
        simp only [integral_const_mul, integral_mul_const]
      _ = _ := by rw [density_sq_integral]; ring
private theorem near_square_snd (u : E) :
    Integrable (fun p : X × X => nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.2) ^ 2) μ₂ ∧
    (∫ p : X × X, nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.2) ^ 2 ∂μ₂) =
      (∫ x, nearKernel x ∂μ) * ‖physicalHartreeDensityL2 u‖ ^ 2 := by
  have he (x y : X) : nearKernel (x - y) = nearKernel (y - x) := by
    rw [← neg_sub y x, near_even]
  have heq : (fun p : X × X => nearKernel (p.1 - p.2) * (physicalHartreeDensityL2 u p.2) ^ 2) =
      (fun p : X × X => nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.2) ^ 2) := by
    funext p
    rw [he p.1 p.2]
  constructor
  · have hi := (near_square u).1.swap
    change Integrable (fun p : X × X =>
      nearKernel (p.1 - p.2) * (physicalHartreeDensityL2 u p.2) ^ 2) μ₂ at hi
    rw [heq] at hi
    exact hi
  · have hi := integral_prod_swap (μ := μ) (ν := μ)
      (fun p : X × X => nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.1) ^ 2)
    change (∫ p : X × X, nearKernel (p.1 - p.2) * (physicalHartreeDensityL2 u p.2) ^ 2 ∂μ₂) =
      (∫ p : X × X, nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.1) ^ 2 ∂μ₂) at hi
    rw [heq, (near_square u).2] at hi
    exact hi
private def kernelIntegrand (u v : E) (p : X × X) : ℝ :=
  physicalHartreeKernel (p.2 - p.1) * physicalHartreeDensityL2 u p.1 * physicalHartreeDensityL2 v p.2
private def majorant (u v : E) (p : X × X) : ℝ :=
  (nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.1) ^ 2 +
    nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 v p.2) ^ 2) / 2 +
  ‖physicalHartreeDensityL2 u p.1‖ * ‖physicalHartreeDensityL2 v p.2‖
private theorem majorant_integrable (u v : E) : Integrable (majorant u v) μ₂ :=
  (((near_square u).1.add (near_square_snd v).1).div_const 2).add
    ((density_integrable u).norm.mul_prod (density_integrable v).norm)
private theorem integrand_le_majorant (u v : E) (p : X × X) :
    ‖kernelIntegrand u v p‖ ≤ majorant u v p := by
  let a := physicalHartreeDensityL2 u p.1
  let b := physicalHartreeDensityL2 v p.2
  have hk := kernel_le_near_add_one (p.2 - p.1)
  have hn := near_nonneg (p.2 - p.1)
  have hc : physicalHartreeKernel (p.2 - p.1) ≥ 0 := inv_nonneg.mpr (sq_nonneg _)
  have hprod := mul_le_mul_of_nonneg_right hk (mul_nonneg (norm_nonneg a) (norm_nonneg b))
  have hab : 2 * ‖a‖ * ‖b‖ ≤ a ^ 2 + b ^ 2 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hnear := mul_le_mul_of_nonneg_left hab hn
  change ‖physicalHartreeKernel (p.2 - p.1) * a * b‖ ≤
    (nearKernel (p.2 - p.1) * a ^ 2 + nearKernel (p.2 - p.1) * b ^ 2) / 2 + ‖a‖ * ‖b‖
  rw [norm_mul, norm_mul, Real.norm_of_nonneg hc]
  nlinarith only [hprod, hnear]
private theorem kernel_integrable (u v : E) : Integrable (kernelIntegrand u v) μ₂ := by
  apply (majorant_integrable u v).mono'
  · exact (((kernel_meas.comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable (physicalHartreeDensityL2 u)).comp_fst).mul
      (Lp.aestronglyMeasurable (physicalHartreeDensityL2 v)).comp_snd
  · exact Filter.Eventually.of_forall (integrand_le_majorant u v)
private theorem majorant_integral (u v : E) :
    (∫ p, majorant u v p ∂μ₂) =
      (∫ x, nearKernel x ∂μ) / 2 * (‖physicalHartreeDensityL2 u‖ ^ 2 + ‖physicalHartreeDensityL2 v‖ ^ 2) +
      ‖physicalHartreeDensityL1 u‖ * ‖physicalHartreeDensityL1 v‖ := by
  have hA : Integrable (fun p : X × X =>
      (nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 u p.1) ^ 2 +
        nearKernel (p.2 - p.1) * (physicalHartreeDensityL2 v p.2) ^ 2) / 2) μ₂ :=
    ((near_square u).1.add (near_square_snd v).1).div_const 2
  have hB : Integrable (fun p : X × X =>
      ‖physicalHartreeDensityL2 u p.1‖ * ‖physicalHartreeDensityL2 v p.2‖) μ₂ :=
    (density_integrable u).norm.mul_prod (density_integrable v).norm
  unfold majorant
  rw [integral_add hA hB]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,
    integral_add (near_square u).1 (near_square_snd v).1,
    (near_square u).2, (near_square_snd v).2]
  rw [integral_prod _ hB]
  simp only [integral_const_mul, integral_mul_const, density_norm_integral]
  ring

/-- Finite bound from derived density norms and the actual integrable near kernel. -/
def physicalNonlocalBound : ℝ :=
  (∫ x, nearKernel x ∂μ) * ‖physicalHartreeDensityL2‖ ^ 2 + ‖physicalHartreeDensityL1‖ ^ 2
private theorem bound_nonneg : 0 ≤ physicalNonlocalBound := by
  exact add_nonneg (mul_nonneg (integral_nonneg near_nonneg) (sq_nonneg _)) (sq_nonneg _)
private theorem square_bound (u v : E) :
    ‖∫ p, kernelIntegrand u v p ∂μ₂‖ ≤ physicalNonlocalBound / 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hn : 0 ≤ ∫ x, nearKernel x ∂μ := integral_nonneg near_nonneg
  have h0 := (norm_integral_le_integral_norm (kernelIntegrand u v)).trans
    (integral_mono (kernel_integrable u v).norm (majorant_integrable u v)
      (integrand_le_majorant u v))
  rw [majorant_integral] at h0
  have h2u := pow_le_pow_left₀ (norm_nonneg (physicalHartreeDensityL2 u))
    (physicalHartreeDensityL2.le_opNorm u) 2
  have h2v := pow_le_pow_left₀ (norm_nonneg (physicalHartreeDensityL2 v))
    (physicalHartreeDensityL2.le_opNorm v) 2
  have h2 := mul_le_mul_of_nonneg_left (add_le_add h2u h2v) hn
  have h1 := mul_le_mul (physicalHartreeDensityL1.le_opNorm u)
    (physicalHartreeDensityL1.le_opNorm v) (norm_nonneg _) (by positivity)
  have hm := mul_nonneg (sq_nonneg ‖physicalHartreeDensityL1‖) (sq_nonneg (‖u‖ - ‖v‖))
  unfold physicalNonlocalBound
  nlinarith only [h0, h2, h1, hm]
private def nonlocalLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∫ p, kernelIntegrand u v p ∂μ₂)
    (by
      intro u v w
      rw [← integral_add (kernel_integrable u w) (kernel_integrable v w)]
      apply integral_congr_ae
      have ha := ae_fst (Lp.coeFn_add (physicalHartreeDensityL2 u) (physicalHartreeDensityL2 v))
      filter_upwards [ha] with p hp
      unfold kernelIntegrand
      rw [map_add, hp]
      simp only [Pi.add_apply]
      ring)
    (by
      intro c u v
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      have ha := ae_fst (Lp.coeFn_smul c (physicalHartreeDensityL2 u))
      filter_upwards [ha] with p hp
      unfold kernelIntegrand
      rw [map_smul, hp]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      intro u v w
      rw [← integral_add (kernel_integrable u v) (kernel_integrable u w)]
      apply integral_congr_ae
      have ha := ae_snd (Lp.coeFn_add (physicalHartreeDensityL2 v) (physicalHartreeDensityL2 w))
      filter_upwards [ha] with p hp
      unfold kernelIntegrand
      rw [map_add, hp]
      simp only [Pi.add_apply]
      ring)
    (by
      intro c u v
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      have ha := ae_snd (Lp.coeFn_smul c (physicalHartreeDensityL2 v))
      filter_upwards [ha] with p hp
      unfold kernelIntegrand
      rw [map_smul, hp]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
private theorem product_bound (u v : E) :
    ‖nonlocalLinear u v‖ ≤ physicalNonlocalBound * ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hb := square_bound (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)
  change ‖nonlocalLinear (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)‖ ≤ _ at hb
  have hu' : ‖‖u‖⁻¹ • u‖ = 1 := by simp [norm_smul, hnu.ne']
  have hv' : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, hnv.ne']
  rw [hu', hv'] at hb
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_norm] at hb
  have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hnu.le hnv.le)
  have he : ‖u‖ * ‖v‖ * (‖u‖⁻¹ * (‖v‖⁻¹ * ‖nonlocalLinear u v‖)) = ‖nonlocalLinear u v‖ := by
    field_simp
  nlinarith only [hh, he]

/-- Bounded bilinear form constructed from the actual singular integral. -/
def physicalNonlocalFormCLM : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ nonlocalLinear physicalNonlocalBound product_bound
/-- Actual 3D double integral, not a definition by radial energy coordinates. -/
def physicalNonlocalForm (u v : E) : ℝ :=
  ∫ p : X × X, physicalHartreeKernel (p.2 - p.1) *
    (physicalCubicWeight p.1 * physicalL6Realization u p.1) *
    (physicalCubicWeight p.2 * physicalL6Realization v p.2) ∂μ₂
private theorem actual_integrand_ae (u v : E) :
    kernelIntegrand u v =ᵐ[μ₂] (fun p : X × X => physicalHartreeKernel (p.2 - p.1) *
      (physicalCubicWeight p.1 * physicalL6Realization u p.1) *
      (physicalCubicWeight p.2 * physicalL6Realization v p.2)) := by
  filter_upwards [ae_fst (density2_ae u), ae_snd (density2_ae v)] with p hu hv
  unfold kernelIntegrand
  rw [hu, hv]
private theorem form_eq (u v : E) : physicalNonlocalForm u v = physicalNonlocalFormCLM u v :=
  (integral_congr_ae (actual_integrand_ae u v)).symm
private theorem form_symm (u v : E) : physicalNonlocalForm u v = physicalNonlocalForm v u := by
  rw [form_eq, form_eq]
  change (∫ p, kernelIntegrand u v p ∂μ₂) = ∫ p, kernelIntegrand v u p ∂μ₂
  rw [← integral_prod_swap (kernelIntegrand v u)]
  apply integral_congr_ae
  filter_upwards with p
  unfold kernelIntegrand physicalHartreeKernel
  change (‖p.2 - p.1‖ ^ 2)⁻¹ * physicalHartreeDensityL2 u p.1 * physicalHartreeDensityL2 v p.2 =
    (‖p.1 - p.2‖ ^ 2)⁻¹ * physicalHartreeDensityL2 v p.2 * physicalHartreeDensityL2 u p.1
  rw [norm_sub_rev p.1 p.2]
  ring

/-- One complete R18 environment. Physical density membership and singular
product integrability are conclusions, not terminal hypotheses. -/
theorem physicalNonlocalForm_certified :
    (∀ u : E, Integrable (fun x => physicalCubicWeight x * physicalL6Realization u x) μ ∧
      MemLp (fun x => physicalCubicWeight x * physicalL6Realization u x) 2 μ) ∧
    (∀ u v : E, Integrable (fun p : X × X => physicalHartreeKernel (p.2 - p.1) *
      (physicalCubicWeight p.1 * physicalL6Realization u p.1) *
      (physicalCubicWeight p.2 * physicalL6Realization v p.2)) μ₂) ∧
    (∀ u v : E, physicalNonlocalForm u v = physicalNonlocalFormCLM u v) ∧
    Continuous (fun p : E × E => physicalNonlocalForm p.1 p.2) ∧
    0 ≤ physicalNonlocalBound ∧
    (∀ u v : E, |physicalNonlocalForm u v| ≤ physicalNonlocalBound * ‖u‖ * ‖v‖) ∧
    (∀ u v : E, physicalNonlocalForm u v = physicalNonlocalForm v u) ∧
    (∀ u v : E, physicalNonlocalForm u v =
      ∫ x : X, ∫ y : X, physicalHartreeKernel (y - x) *
        (physicalCubicWeight x * physicalL6Realization u x) *
        (physicalCubicWeight y * physicalL6Realization v y)) ∧
    (∀ u v : E, ∀ un vn : ℕ → E,
      Tendsto un atTop (𝓝 u) → Tendsto vn atTop (𝓝 v) →
      Tendsto (fun n => physicalNonlocalForm (un n) (vn n)) atTop (𝓝 (physicalNonlocalForm u v))) := by
  have hc : Continuous (fun p : E × E => physicalNonlocalForm p.1 p.2) := by
    simp_rw [form_eq]
    exact physicalNonlocalFormCLM.continuous₂
  refine ⟨?_, ?_, form_eq, hc, bound_nonneg, ?_, form_symm, ?_, ?_⟩
  · intro u
    exact ⟨(density_integrable u).congr (density2_ae u),
      (memLp_congr_ae (density2_ae u)).mp (Lp.memLp (physicalHartreeDensityL2 u))⟩
  · intro u v
    exact (kernel_integrable u v).congr (actual_integrand_ae u v)
  · intro u v
    rw [form_eq]
    exact product_bound u v
  · intro u v
    exact integral_prod _ ((kernel_integrable u v).congr (actual_integrand_ae u v))
  · intro u v un vn hu hv
    have hp : Tendsto (fun n => (un n, vn n)) atTop (𝓝 (u, v)) := hu.prodMk_nhds hv
    have ht := (hc.tendsto (u, v)).comp hp
    exact ht
end HBL.Modulation.Monopole
