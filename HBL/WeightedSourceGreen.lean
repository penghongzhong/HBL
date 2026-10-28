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
  have hpow : IntegrableOn
      (fun rho : ℝ => rho * (1 + rho ^ 2) ^ (-sigma)) (Ioi 0) := by
    have hderiv : ∀ rho : ℝ, 0 < rho →
        HasDerivAt
          (fun x : ℝ => -(1 / (2 * (sigma - 1))) *
            (1 + x ^ 2) ^ (1 - sigma))
          (rho * (1 + rho ^ 2) ^ (-sigma)) rho := by
      intro rho hr
      have hbase :
          HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * rho) rho := by
        convert (hasDerivAt_const rho (1 : ℝ)).add ((hasDerivAt_id rho).pow 2) using 1 <;> ring
      have hp := hbase.rpow_const (by positivity : 0 < 1 + rho ^ 2) (1 - sigma)
      convert hp.const_mul (-(1 / (2 * (sigma - 1)))) using 1
      · ring
      · have hs : sigma - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hsigma)
        have hb : 1 + rho ^ 2 ≠ 0 := by positivity
        rw [Real.rpow_sub_one (by positivity : 0 < 1 + rho ^ 2)]
        field_simp [hs, hb]
        ring
    have htail :
        Tendsto
          (fun x : ℝ => -(1 / (2 * (sigma - 1))) *
            (1 + x ^ 2) ^ (1 - sigma))
          atTop (𝓝 0) := by
      have hexp : 1 - sigma < 0 := sub_neg.mpr hsigma
      have hbase : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop := by
        exact tendsto_atTop_add_const_right _ 1
          (tendsto_pow_atTop_atTop_of_one_lt 2 (by norm_num))
      have hp := Real.tendsto_rpow_neg_atTop hexp
      have hcomp := hp.comp hbase
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcomp)
    have hloc :
        IntegrableOn
          (fun rho : ℝ => rho * (1 + rho ^ 2) ^ (-sigma)) (Ioc 0 1) :=
      ((continuous_id.mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun r => Or.inl (by positivity)))).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have htailInt :
        IntegrableOn
          (fun rho : ℝ => rho * (1 + rho ^ 2) ^ (-sigma)) (Ioi 1) := by
      have hprim :=
        integral_Ioi_of_hasDerivAt_of_tendsto
          ((hderiv 1 (by norm_num)).continuousAt.continuousWithinAt)
          (fun x hx => hderiv x (by linarith [hx]))
          ?_ htail
      · exact hprim.1
      · exact
          ((continuous_id.mul
            ((continuous_const.add (continuous_id.pow 2)).rpow_const
              (fun r => Or.inl (by positivity)))).continuousOn.integrableOn_Icc).mono_set
            (by intro x hx; exact ⟨by linarith [hx.1], le_rfl⟩)
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hloc.union htailInt
  have hneg : IntegrableOn (weightedSourceMajorant sigma) (Iio 0) := by
    have href := hpow.comp_neg
    simpa [weightedSourceMajorant, abs_of_neg] using href
  have hpos : IntegrableOn (weightedSourceMajorant sigma) (Ioi 0) := by
    refine hpow.congr_fun ?_ measurableSet_Ioi
    intro rho hr
    rw [weightedSourceMajorant, abs_of_pos hr]
  rw [← integrableOn_Iio_union_Ioi]
  exact hneg.union hpos

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
  rw [abs_of_pos hr, abs_of_pos hrho, hdec]
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
