import HBL.AngularGreenResolvent
import HBL.L2KernelComposition

/-!
The weighted zero-energy Green operator and the two concrete composition
identities needed for the Hartree Birman--Schwinger polynomial.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace HBL.L2Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem operator_sub (K L : RealKernelL2 μ) :
    operator (K - L) = operator K - operator L := by
  rw [sub_eq_add_neg, show -L = (-1 : ℝ) • L by simp,
    operator_add, operator_smul]
  module

end HBL.L2Kernel

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem angularZeroGreen_nonneg_of_mem
    {theta phi : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hphi : phi ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ angularZeroGreen theta phi := by
  unfold angularZeroGreen
  have hmin : 0 ≤ min theta phi := le_min htheta.1 hphi.1
  have hmax : max theta phi ≤ Real.pi / 2 := max_le htheta.2 hphi.2
  exact mul_nonneg
    (mul_nonneg (by positivity) hmin) (sub_nonneg.mpr hmax)

theorem angularZeroGreen_le_pi_div_two
    {theta phi : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hphi : phi ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    angularZeroGreen theta phi ≤ Real.pi / 2 := by
  have hmin0 : 0 ≤ min theta phi := le_min htheta.1 hphi.1
  have hminle : min theta phi ≤ Real.pi / 2 :=
    (min_le_left theta phi).trans htheta.2
  have hmax0 : 0 ≤ max theta phi :=
    htheta.1.trans (le_max_left theta phi)
  have hmaxle : max theta phi ≤ Real.pi / 2 := max_le htheta.2 hphi.2
  have htail0 : 0 ≤ Real.pi / 2 - max theta phi := sub_nonneg.mpr hmaxle
  have htaille : Real.pi / 2 - max theta phi ≤ Real.pi / 2 := by
    linarith
  have hprod : min theta phi * (Real.pi / 2 - max theta phi) ≤
      (Real.pi / 2) * (Real.pi / 2) :=
    mul_le_mul hminle htaille htail0 (by positivity)
  unfold angularZeroGreen
  calc
    2 / Real.pi * min theta phi * (Real.pi / 2 - max theta phi) =
        (2 / Real.pi) *
          (min theta phi * (Real.pi / 2 - max theta phi)) := by ring
    _ ≤ (2 / Real.pi) * ((Real.pi / 2) * (Real.pi / 2)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = Real.pi / 2 := by field_simp [Real.pi_ne_zero]

theorem weightedZeroGreen_uncurry_continuous :
    Continuous (Function.uncurry weightedZeroGreen) := by
  unfold Function.uncurry weightedZeroGreen angularZeroGreen
  apply Continuous.mul
  · exact (bubble_contDiff_infty.continuous.comp continuous_fst).mul
      (bubble_contDiff_infty.continuous.comp continuous_snd)
  · fun_prop

theorem weightedZeroGreen_nonneg
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    0 ≤ weightedZeroGreen r rho := by
  have htheta : Real.arctan r ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(Real.arctan_pos.mpr hr).le, (Real.arctan_lt_pi_div_two r).le⟩
  have hphi : Real.arctan rho ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(Real.arctan_pos.mpr hrho).le,
      (Real.arctan_lt_pi_div_two rho).le⟩
  unfold weightedZeroGreen
  exact mul_nonneg
    (mul_nonneg
      (show 0 ≤ bubble r by unfold bubble; positivity)
      (show 0 ≤ bubble rho by unfold bubble; positivity))
    (angularZeroGreen_nonneg_of_mem htheta hphi)

theorem weightedZeroGreen_sq_le_majorant
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    weightedZeroGreen r rho ^ 2 ≤
      (Real.pi / 2) ^ 2 *
        (birmanSquareWeight r * birmanSquareWeight rho) := by
  have htheta : Real.arctan r ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(Real.arctan_pos.mpr hr).le, (Real.arctan_lt_pi_div_two r).le⟩
  have hphi : Real.arctan rho ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(Real.arctan_pos.mpr hrho).le,
      (Real.arctan_lt_pi_div_two rho).le⟩
  have hD0 := angularZeroGreen_nonneg_of_mem htheta hphi
  have hDle := angularZeroGreen_le_pi_div_two htheta hphi
  have hDsq : angularZeroGreen (Real.arctan r) (Real.arctan rho) ^ 2 ≤
      (Real.pi / 2) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hD0 hDle
  have hw : 0 ≤ bubble r ^ 2 * bubble rho ^ 2 := by positivity
  unfold weightedZeroGreen birmanSquareWeight
  calc
    (bubble r * bubble rho *
        angularZeroGreen (Real.arctan r) (Real.arctan rho)) ^ 2 =
        (bubble r ^ 2 * bubble rho ^ 2) *
          angularZeroGreen (Real.arctan r) (Real.arctan rho) ^ 2 := by ring
    _ ≤ (bubble r ^ 2 * bubble rho ^ 2) * (Real.pi / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hDsq hw
    _ = (Real.pi / 2) ^ 2 * (bubble r ^ 2 * bubble rho ^ 2) := by ring

theorem weightedZeroGreen_sq_integrable :
    Integrable (fun p : ℝ × ℝ => weightedZeroGreen p.1 p.2 ^ 2)
      (halfLineMeasure.prod halfLineMeasure) := by
  rw [halfLineMeasure, Measure.prod_restrict]
  have hmajor : IntegrableOn
      (fun p : ℝ × ℝ => (Real.pi / 2) ^ 2 *
        (birmanSquareWeight p.1 * birmanSquareWeight p.2))
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (volume.prod volume) :=
    ((birmanSquareWeight_integrable.mul_prod
      birmanSquareWeight_integrable).const_mul ((Real.pi / 2) ^ 2)).integrableOn
  refine hmajor.mono'
    ((weightedZeroGreen_uncurry_continuous.pow 2).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact weightedZeroGreen_sq_le_majorant hp.1 hp.2

theorem weightedZeroGreen_memLp_two :
    MemLp (Function.uncurry weightedZeroGreen) 2
      (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq
    weightedZeroGreen_uncurry_continuous.aestronglyMeasurable).2
  exact weightedZeroGreen_sq_integrable

def weightedZeroGreenL2 : RealKernelL2 halfLineMeasure :=
  weightedZeroGreen_memLp_two.toLp (Function.uncurry weightedZeroGreen)

theorem weightedZeroGreenL2_ae :
    (weightedZeroGreenL2 : ℝ × ℝ → ℝ) =ᵐ[
      halfLineMeasure.prod halfLineMeasure]
      Function.uncurry weightedZeroGreen :=
  weightedZeroGreen_memLp_two.coeFn_toLp

def weightedZeroGreenOperator :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  operator weightedZeroGreenL2

theorem weightedFreeGreen_nonneg
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    0 ≤ weightedFreeGreen r rho := by
  unfold weightedFreeGreen
  exact mul_nonneg (mul_nonneg (lt_min hr hrho).le (by positivity))
    (by positivity)

theorem weightedHartreeKernel_nonneg
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    0 ≤ weightedHartreeKernel r rho := by
  have hkappa : 0 ≤ hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hbr : 0 ≤ bubble r := by
    unfold bubble
    positivity
  have hbrho : 0 ≤ bubble rho := by
    unfold bubble
    positivity
  have hlog := hartreeRadialLog_nonneg r rho hr hrho
  unfold weightedHartreeKernel
  positivity

theorem weightedHartreeOperator_square :
    weightedHartreeOperator ∘L weightedHartreeOperator =
      (576 : ℝ) • weightedZeroGreenOperator := by
  let m : ℝ → ℝ → ℝ := Function.curry
    ((576 : ℝ) • Function.uncurry weightedZeroGreen)
  have hm : MemLp (Function.uncurry m) 2
      (halfLineMeasure.prod halfLineMeasure) := by
    simpa [m] using
      weightedZeroGreen_memLp_two.const_smul (576 : ℝ)
  have hcomp := operator_comp_toLp_eq_of_convolution
    (μ := halfLineMeasure) (fun r : ℝ => 0 < r)
    (ae_restrict_mem measurableSet_Ioi)
    weightedHartreeKernel weightedHartreeKernel m
    weightedHartreeKernel_memLp_two weightedHartreeKernel_memLp_two hm
    (fun r rho hr hrho => weightedHartreeKernel_nonneg hr hrho)
    (fun r rho hr hrho => weightedHartreeKernel_nonneg hr hrho)
    (fun r rho hr hrho => by
      rw [halfLineMeasure]
      change (∫ s in Ioi (0 : ℝ),
        weightedHartreeKernel r s * weightedHartreeKernel s rho) =
          576 * weightedZeroGreen r rho
      exact weightedHartreeKernel_square_integral hr hrho)
  have hmL2 : hm.toLp (Function.uncurry m) =
      (576 : ℝ) • weightedZeroGreenL2 := by
    simpa [m, weightedZeroGreenL2] using
      (MemLp.toLp_const_smul (576 : ℝ) weightedZeroGreen_memLp_two)
  change operator weightedHartreeKernelL2 ∘L
      operator weightedHartreeKernelL2 =
    (576 : ℝ) • operator weightedZeroGreenL2
  rw [← operator_smul]
  rw [← hmL2]
  exact hcomp

theorem weightedZeroGreenOperator_comp_free :
    weightedZeroGreenOperator ∘L weightedFreeGreenOperator =
      weightedFreeGreenOperator - weightedZeroGreenOperator := by
  let m : ℝ → ℝ → ℝ := Function.curry
    (Function.uncurry weightedFreeGreen -
      Function.uncurry weightedZeroGreen)
  have hm : MemLp (Function.uncurry m) 2
      (halfLineMeasure.prod halfLineMeasure) := by
    simpa [m] using
      weightedFreeGreen_memLp_two.sub weightedZeroGreen_memLp_two
  have hcomp := operator_comp_toLp_eq_of_convolution
    (μ := halfLineMeasure) (fun r : ℝ => 0 < r)
    (ae_restrict_mem measurableSet_Ioi)
    weightedZeroGreen weightedFreeGreen m
    weightedZeroGreen_memLp_two weightedFreeGreen_memLp_two hm
    (fun r rho hr hrho => weightedZeroGreen_nonneg hr hrho)
    (fun r rho hr hrho => weightedFreeGreen_nonneg hr hrho)
    (fun r rho hr hrho => by
      rw [halfLineMeasure]
      change (∫ s in Ioi (0 : ℝ),
        weightedZeroGreen r s * weightedFreeGreen s rho) =
          weightedFreeGreen r rho - weightedZeroGreen r rho
      linarith [weightedZeroGreen_free_resolvent_integral hr hrho])
  have hmL2 : hm.toLp (Function.uncurry m) =
      weightedFreeGreenL2 - weightedZeroGreenL2 := by
    simpa [m, weightedFreeGreenL2, weightedZeroGreenL2] using
      (MemLp.toLp_sub weightedFreeGreen_memLp_two
        weightedZeroGreen_memLp_two)
  change operator weightedZeroGreenL2 ∘L operator weightedFreeGreenL2 =
    operator weightedFreeGreenL2 - operator weightedZeroGreenL2
  rw [← operator_sub]
  rw [← hmL2]
  exact hcomp

theorem weightedZeroGreen_resolvent (z : RealL2 halfLineMeasure) :
    weightedZeroGreenOperator (z + weightedFreeGreenOperator z) =
      weightedFreeGreenOperator z := by
  rw [map_add]
  have hcomp := congrArg
    (fun T : RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure => T z)
    weightedZeroGreenOperator_comp_free
  simp only [ContinuousLinearMap.comp_apply, sub_apply] at hcomp
  rw [hcomp]
  module

end HBL.Modulation.Monopole
