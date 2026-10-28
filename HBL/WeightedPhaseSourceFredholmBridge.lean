import HBL.WeightedPhaseGreenPrimitive
import HBL.WeightedPhaseSourceChargeGeneral
import HBL.WeightedSourceFredholmBridge
import HBL.WeightedPhaseFredholmInverse

/-!
# Actual phase-channel cross-space Green/Fredholm inverse

For every physical source F in L^{2,sigma}, sigma>1, the cross-space
Hilbert-Schmidt operator B_sigma is the true endpoint-conjugated free
Green map. Its pairing with the first sine mode is exactly (2/3) times
the physical phase threshold charge.  This removes the artificial
sigma=2 restriction from the earlier physical phase source inverse.

Only the weighted Hilbert integral equation is asserted here.  The
manuscript's classical output L^{2,-sigma}, radial regularity and
exact one-layer nonlinear residual are not claimed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

theorem weightedPhaseSourceGreen_cokernel_pairing
    (sigma : ℝ) (hsigma : 1 < sigma)
    (g : RealL2 halfLineMeasure) :
    inner ℝ (weightedHartreeSineModeL2 1)
        (weightedSourceGreenOperator sigma hsigma g) =
      (2 / 3 : ℝ) * inner ℝ
        (weightedPhaseSourceResonanceL2 sigma (by linarith))
        g := by
  rw [real_inner_comm]
  change inner ℝ
      (operator (weightedSourceGreenKernelL2 sigma hsigma) g)
      (weightedHartreeSineModeL2 1) = _
  rw [inner_operator, L2.inner_def]
  have hprod : Integrable (fun p : ℝ × ℝ =>
      weightedSourceGreenKernel sigma p.1 p.2 *
        (weightedHartreeSineModeL2 1 p.1 * g p.2))
      (halfLineMeasure.prod halfLineMeasure) := by
    have h :=
      (weightedSourceGreenKernel_memLp_two sigma hsigma).integrable_mul
        (Lp.memLp (tensor (weightedHartreeSineModeL2 1) g))
    refine h.congr ?_
    filter_upwards [tensor_ae (weightedHartreeSineModeL2 1) g] with p ht
    change weightedSourceGreenKernel sigma p.1 p.2 *
        (tensor (weightedHartreeSineModeL2 1) g : ℝ × ℝ → ℝ) p = _
    rw [ht]
  have hkernel :
      (fun p : ℝ × ℝ =>
        inner ℝ ((weightedSourceGreenKernelL2 sigma hsigma) p)
          ((tensor (weightedHartreeSineModeL2 1) g) p)) =ᵐ[
          halfLineMeasure.prod halfLineMeasure]
      fun p => weightedSourceGreenKernel sigma p.1 p.2 *
        (weightedHartreeSineModeL2 1 p.1 * g p.2) := by
    filter_upwards [
      weightedSourceGreenKernelL2_ae sigma hsigma,
      tensor_ae (weightedHartreeSineModeL2 1) g] with p hK ht
    rw [hK, ht, Real.inner_apply]
    rfl
  rw [integral_congr_ae hkernel]
  calc
    (∫ p : ℝ × ℝ,
      weightedSourceGreenKernel sigma p.1 p.2 *
        (weightedHartreeSineModeL2 1 p.1 * g p.2)
      ∂(halfLineMeasure.prod halfLineMeasure)) =
        ∫ rho : ℝ, ∫ r : ℝ,
          weightedSourceGreenKernel sigma r rho *
            (weightedHartreeSineModeL2 1 r * g rho)
          ∂halfLineMeasure ∂halfLineMeasure := by
      exact MeasureTheory.integral_prod_symm
        (μ := halfLineMeasure) (ν := halfLineMeasure)
        (fun p : ℝ × ℝ =>
          weightedSourceGreenKernel sigma p.1 p.2 *
            (weightedHartreeSineModeL2 1 p.1 * g p.2)) hprod
    _ = ∫ rho : ℝ,
        weightedGreenPrimitive (weightedHartreeSineModeL2 1) rho *
          (affineJapaneseDecay sigma rho * g rho)
        ∂halfLineMeasure := by
      apply integral_congr_ae
      filter_upwards with rho
      calc
        (∫ r : ℝ,
          weightedSourceGreenKernel sigma r rho *
            (weightedHartreeSineModeL2 1 r * g rho)
          ∂halfLineMeasure) =
            (affineJapaneseDecay sigma rho * g rho) *
              (∫ r : ℝ,
                min rho r *
                  (weightedGreenDecay r * weightedHartreeSineModeL2 1 r)
                ∂halfLineMeasure) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with r
          unfold weightedSourceGreenKernel weightedGreenDecay
          rw [min_comm r rho]
          ring
        _ = weightedGreenPrimitive (weightedHartreeSineModeL2 1) rho *
              (affineJapaneseDecay sigma rho * g rho) := by
          unfold weightedGreenPrimitive
          ring
    _ = ∫ rho : ℝ,
        ((2 / 3 : ℝ) * resonanceMinus rho) *
          (affineJapaneseDecay sigma rho * g rho)
        ∂halfLineMeasure := by
      apply integral_congr_ae
      filter_upwards [weightedPhaseGreenPrimitive_ae] with rho hp
      rw [hp]
    _ = (2 / 3 : ℝ) * inner ℝ
        (weightedPhaseSourceResonanceL2 sigma (by linarith)) g := by
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [
        weightedPhaseSourceResonanceL2_ae sigma (by linarith : 1 / 2 < sigma)]
        with rho hpsi
      rw [hpsi, Real.inner_apply]
      unfold weightedPhaseSourceResonance
      ring

theorem weightedPhaseSourceGreen_cokernel_zero_of_charge_zero
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.minus F = 0) :
    inner ℝ (weightedHartreeSineModeL2 1)
      (weightedSourceGreenOperator sigma hsigma
        (weightedSourceDataL2 sigma F hF)) = 0 := by
  rw [weightedPhaseSourceGreen_cokernel_pairing,
    weightedPhaseSourceResonance_inner_data_eq_pairing, hcharge]
  ring

theorem weightedPhaseSourceGreen_mem_adjointKernel_orthogonal
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.minus F = 0) :
    weightedSourceGreenOperator sigma hsigma
        (weightedSourceDataL2 sigma F hF) ∈
      (ContinuousLinearMap.adjoint (1 - weightedPhaseBirman)).kerᗮ :=
  phaseFredholmSource_mem_cokernel_orthogonal _
    (weightedPhaseSourceGreen_cokernel_zero_of_charge_zero
      sigma hsigma F hF hcharge)

theorem existsUnique_phaseWeightedSourceFredholmSolve
    (sigma : ℝ) (hsigma : 1 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F)
    (hcharge : channelPairing HartreeChannel.minus F = 0) :
    ∃! x : (1 - weightedPhaseBirman).kerᗮ,
      (1 - weightedPhaseBirman) (x : RealL2 halfLineMeasure) =
        weightedSourceGreenOperator sigma hsigma
          (weightedSourceDataL2 sigma F hF) :=
  existsUnique_phaseFredholmSolution _
    (weightedPhaseSourceGreen_cokernel_zero_of_charge_zero
      sigma hsigma F hF hcharge)

#print axioms weightedPhaseSourceGreen_cokernel_pairing
#print axioms weightedPhaseSourceGreen_cokernel_zero_of_charge_zero
#print axioms weightedPhaseSourceGreen_mem_adjointKernel_orthogonal
#print axioms existsUnique_phaseWeightedSourceFredholmSolve

end HBL.Modulation.Monopole
