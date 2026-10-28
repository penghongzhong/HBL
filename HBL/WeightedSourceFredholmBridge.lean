import HBL.WeightedSourceChargeBridge
import HBL.WeightedScaleGreen
import HBL.MonopoleFredholmSolution

/-!
# Cokernel pairing for the weighted source Green map

The source Green map B_sigma is the correct cross-space Green operator for
physical L^{2,sigma} data.  Testing its output against the actual Fredholm
cokernel generator reduces, by the already proved scale Green identity, to
the manuscript affine charge.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

theorem weightedSourceGreen_cokernel_pairing
    (sigma : ℝ) (hsigma : 1 < sigma)
    (g : RealL2 halfLineMeasure) :
    inner ℝ (weightedPotentialOperator weightedScaleResonanceL2)
        (weightedSourceGreenOperator sigma hsigma g) =
      inner ℝ
        (weightedSourceResonanceL2 sigma (by linarith))
        g := by
  rw [weightedPotentialOperator_scale_eigen]
  rw [real_inner_smul_left]
  rw [real_inner_comm]
  change 15 *
      inner ℝ
        (operator (weightedSourceGreenKernelL2 sigma hsigma) g)
        weightedScaleResonanceL2 = _
  rw [inner_operator, L2.inner_def]
  have hprod : Integrable (fun p : ℝ × ℝ =>
      weightedSourceGreenKernel sigma p.1 p.2 *
        (weightedScaleResonanceL2 p.1 * g p.2))
      (halfLineMeasure.prod halfLineMeasure) := by
    have h :=
      (weightedSourceGreenKernel_memLp_two sigma hsigma).integrable_mul
        (Lp.memLp (tensor weightedScaleResonanceL2 g))
    refine h.congr ?_
    filter_upwards [tensor_ae weightedScaleResonanceL2 g] with p ht
    change weightedSourceGreenKernel sigma p.1 p.2 *
        (tensor weightedScaleResonanceL2 g : ℝ × ℝ → ℝ) p = _
    rw [ht]
  have hkernel :
      (fun p : ℝ × ℝ =>
        inner ℝ ((weightedSourceGreenKernelL2 sigma hsigma) p)
          ((tensor weightedScaleResonanceL2 g) p)) =ᵐ[
          halfLineMeasure.prod halfLineMeasure]
      fun p => weightedSourceGreenKernel sigma p.1 p.2 *
        (weightedScaleResonanceL2 p.1 * g p.2) := by
    filter_upwards [
      weightedSourceGreenKernelL2_ae sigma hsigma,
      tensor_ae weightedScaleResonanceL2 g] with p hK ht
    rw [hK, ht, Real.inner_apply]
    rfl
  rw [integral_congr_ae hkernel]
  rw [← integral_const_mul]
  have hprod15 : Integrable (fun p : ℝ × ℝ =>
      15 * (weightedSourceGreenKernel sigma p.1 p.2 *
        (weightedScaleResonanceL2 p.1 * g p.2)))
      (halfLineMeasure.prod halfLineMeasure) :=
    hprod.const_mul 15
  calc
    (∫ p : ℝ × ℝ,
      15 * (weightedSourceGreenKernel sigma p.1 p.2 *
        (weightedScaleResonanceL2 p.1 * g p.2))
      ∂(halfLineMeasure.prod halfLineMeasure)) =
        ∫ rho : ℝ, ∫ r : ℝ,
          15 * (weightedSourceGreenKernel sigma r rho *
            (weightedScaleResonanceL2 r * g rho))
          ∂halfLineMeasure ∂halfLineMeasure := by
      exact MeasureTheory.integral_prod_symm
        (μ := halfLineMeasure) (ν := halfLineMeasure)
        (fun p : ℝ × ℝ =>
          15 * (weightedSourceGreenKernel sigma p.1 p.2 *
            (weightedScaleResonanceL2 p.1 * g p.2))) hprod15
    _ = ∫ rho : ℝ,
        weightedSourceResonance sigma rho * g rho
        ∂halfLineMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
      calc
        (∫ r : ℝ,
          15 * (weightedSourceGreenKernel sigma r rho *
            (weightedScaleResonanceL2 r * g rho))
          ∂halfLineMeasure) =
            affineJapaneseDecay sigma rho * g rho *
              (∫ r in Ioi (0 : ℝ),
                min rho r * weightedScaleGreenSource r) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [weightedScaleResonanceL2_ae] with r hx0
          rw [hx0]
          unfold weightedSourceGreenKernel weightedScaleGreenSource
            weightedScaleResonance
          rw [weightedScaleResonance_closed]
          ring
        _ = affineJapaneseDecay sigma rho * g rho *
              resonancePlus rho := by
          rw [min_weightedScaleGreenSource_integral rho hrho]
        _ = weightedSourceResonance sigma rho * g rho := by
          unfold weightedSourceResonance
          ring
    _ = inner ℝ
        (weightedSourceResonanceL2 sigma (by linarith)) g := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        weightedSourceResonanceL2_ae sigma (by linarith : 1 / 2 < sigma)]
        with rho hpsi
      rw [hpsi, Real.inner_apply]

theorem weightedSourceGreen_cokernel_zero_of_charge_zero
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0) :
    inner ℝ (weightedPotentialOperator weightedScaleResonanceL2)
      (weightedSourceGreenOperator sigma hsigma
        (weightedSourceDataL2 sigma F hF)) = 0 := by
  rw [weightedSourceGreen_cokernel_pairing]
  rw [weightedSourceResonance_inner_data_eq_pairing]
  exact hcharge

theorem weightedSourceGreen_mem_adjointKernel_orthogonal
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.plus F = 0) :
    weightedSourceGreenOperator sigma hsigma
        (weightedSourceDataL2 sigma F hF) ∈
      (ContinuousLinearMap.adjoint
        (1 - weightedBirmanSchwingerOperator)).kerᗮ := by
  rw [adjoint_one_sub_weightedBirmanSchwinger_kernel,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact weightedSourceGreen_cokernel_zero_of_charge_zero
    sigma hsigma F hF hcharge

#print axioms weightedSourceGreen_cokernel_pairing
#print axioms weightedSourceGreen_cokernel_zero_of_charge_zero
#print axioms weightedSourceGreen_mem_adjointKernel_orthogonal

end HBL.Modulation.Monopole
