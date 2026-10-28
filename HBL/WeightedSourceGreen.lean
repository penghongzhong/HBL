import HBL.WeightedFreeGreen
import HBL.AffineTailLemmaClosed
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# Free Green input from the manuscript weighted source space

For a physical source F in L^{2,sigma}, write
  g(r) = <r>^sigma F(r).
The endpoint-conjugated free Green output is represented on ordinary
half-line L2 by the cross-kernel

  B_sigma(r,rho) = min(r,rho) (1+r^2)^(-1)
                    (1+rho^2)^(-sigma/2).

For sigma > 1 this kernel is product-L2; the manuscript range
3/2 < sigma < 2 is therefore covered.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

def weightedSourceGreenKernel (sigma r rho : ℝ) : ℝ :=
  min r rho * (1 + r ^ 2)⁻¹ * affineJapaneseDecay sigma rho

theorem weightedSourceGreenKernel_uncurry_continuous (sigma : ℝ) :
    Continuous (Function.uncurry (weightedSourceGreenKernel sigma)) := by
  unfold weightedSourceGreenKernel Function.uncurry
  have hr : Continuous (fun p : ℝ × ℝ => 1 + p.1 ^ 2) := by fun_prop
  exact ((continuous_fst.min continuous_snd).mul
    (hr.inv₀ (fun p => by positivity))).mul
    ((affineJapaneseDecay_continuous sigma).comp continuous_snd)

def weightedSourceMajorant (sigma rho : ℝ) : ℝ :=
  |rho| * (1 + rho ^ 2) ^ (-sigma)

theorem weightedSourceMajorant_nonneg (sigma rho : ℝ) :
    0 ≤ weightedSourceMajorant sigma rho := by
  unfold weightedSourceMajorant
  positivity

theorem weightedSourceMajorant_continuous (sigma : ℝ) :
    Continuous (weightedSourceMajorant sigma) := by
  unfold weightedSourceMajorant
  exact continuous_abs.mul
    ((continuous_const.add (continuous_id.pow 2)).rpow_const
      (fun r => Or.inl (by positivity)))

theorem weightedSourceMajorant_integrable
    (sigma : ℝ) (hsigma : 1 < sigma) :
    Integrable (weightedSourceMajorant sigma) := by
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 * sigma - 1 := by
    rw [Module.finrank_self]
    norm_num
    linarith
  have hbase :
      Integrable (fun rho : ℝ =>
        (1 + rho ^ 2) ^ (1 / 2 - sigma)) := by
    have h := integrable_rpow_neg_one_add_norm_sq
      (E := ℝ) (μ := volume) hdim
    simp only [Real.norm_eq_abs, sq_abs] at h
    convert h using 1
    funext rho
    congr 2
    ring
  refine hbase.mono'
    (weightedSourceMajorant_continuous sigma).aestronglyMeasurable
    (Filter.Eventually.of_forall fun rho => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (weightedSourceMajorant_nonneg sigma rho)]
  have hsqrt : |rho| ≤ Real.sqrt (1 + rho ^ 2) := by
    rw [Real.le_sqrt (abs_nonneg rho) (by positivity)]
    nlinarith [sq_abs rho]
  have hpow0 : 0 ≤ (1 + rho ^ 2) ^ (-sigma) :=
    Real.rpow_nonneg (by positivity) _
  calc
    weightedSourceMajorant sigma rho =
        |rho| * (1 + rho ^ 2) ^ (-sigma) := rfl
    _ ≤ Real.sqrt (1 + rho ^ 2) *
        (1 + rho ^ 2) ^ (-sigma) :=
      mul_le_mul_of_nonneg_right hsqrt hpow0
    _ = (1 + rho ^ 2) ^ (1 / 2 - sigma) := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_add (by positivity : 0 < 1 + rho ^ 2)]
      congr 1
      ring

theorem weightedSourceGreenKernel_sq_le
    (sigma : ℝ) {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    weightedSourceGreenKernel sigma r rho ^ 2 ≤
      freeGreenMajorant r * weightedSourceMajorant sigma rho := by
  have hmin := min_sq_le_mul_of_pos hr hrho
  have hdec :
      affineJapaneseDecay sigma rho ^ 2 =
        (1 + rho ^ 2) ^ (-sigma) :=
    affineJapaneseDecay_sq sigma rho
  have hnonneg :
      0 ≤ (1 + r ^ 2)⁻¹ ^ 2 *
        affineJapaneseDecay sigma rho ^ 2 := by positivity
  unfold weightedSourceGreenKernel freeGreenMajorant weightedSourceMajorant
  rw [abs_of_pos hr, abs_of_pos hrho]
  calc
    (min r rho * (1 + r ^ 2)⁻¹ * affineJapaneseDecay sigma rho) ^ 2 =
        min r rho ^ 2 *
          ((1 + r ^ 2)⁻¹ ^ 2 *
            affineJapaneseDecay sigma rho ^ 2) := by ring
    _ ≤ (r * rho) *
          ((1 + r ^ 2)⁻¹ ^ 2 *
            affineJapaneseDecay sigma rho ^ 2) :=
      mul_le_mul_of_nonneg_right hmin hnonneg
    _ = (r * (1 + r ^ 2)⁻¹ ^ 2) *
          (rho * (1 + rho ^ 2) ^ (-sigma)) := by
      rw [hdec]
      ring

theorem weightedSourceGreenKernel_sq_integrable
    (sigma : ℝ) (hsigma : 1 < sigma) :
    Integrable
      (fun p : ℝ × ℝ =>
        weightedSourceGreenKernel sigma p.1 p.2 ^ 2)
      (halfLineMeasure.prod halfLineMeasure) := by
  rw [halfLineMeasure, Measure.prod_restrict]
  have hmajor : IntegrableOn
      (fun p : ℝ × ℝ =>
        freeGreenMajorant p.1 * weightedSourceMajorant sigma p.2)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (volume.prod volume) :=
    (freeGreenMajorant_integrable.mul_prod
      (weightedSourceMajorant_integrable sigma hsigma)).integrableOn
  refine hmajor.mono'
    ((weightedSourceGreenKernel_uncurry_continuous sigma).pow 2
      |>.aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact weightedSourceGreenKernel_sq_le sigma hp.1 hp.2

theorem weightedSourceGreenKernel_memLp_two
    (sigma : ℝ) (hsigma : 1 < sigma) :
    MemLp (Function.uncurry (weightedSourceGreenKernel sigma)) 2
      (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq
    (weightedSourceGreenKernel_uncurry_continuous sigma).aestronglyMeasurable).2
  exact weightedSourceGreenKernel_sq_integrable sigma hsigma

def weightedSourceGreenKernelL2
    (sigma : ℝ) (hsigma : 1 < sigma) :
    RealKernelL2 halfLineMeasure :=
  (weightedSourceGreenKernel_memLp_two sigma hsigma).toLp
    (Function.uncurry (weightedSourceGreenKernel sigma))

def weightedSourceGreenOperator
    (sigma : ℝ) (hsigma : 1 < sigma) :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  operator (weightedSourceGreenKernelL2 sigma hsigma)

theorem weightedSourceGreenOperator_kernel_certificate
    (sigma : ℝ) (hsigma : 1 < sigma) :
    IsHilbertSchmidtKernelOperator
      (weightedSourceGreenOperator sigma hsigma)
      (weightedSourceGreenKernelL2 sigma hsigma) :=
  operator_isHilbertSchmidtKernelOperator
    (weightedSourceGreenKernelL2 sigma hsigma)

#print axioms weightedSourceGreenKernel_sq_integrable
#print axioms weightedSourceGreenKernel_memLp_two
#print axioms weightedSourceGreenOperator_kernel_certificate

end HBL.Modulation.Monopole
