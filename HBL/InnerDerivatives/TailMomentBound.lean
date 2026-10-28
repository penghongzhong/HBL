import HBL.InnerDerivatives.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail HBL.Profile.ActualInner

theorem halfLineGreenTail_moment_bound (S : ℝ → ℝ)
    (hS : Integrable S halfLineMeasure)
    (hM : Integrable (fun r => r * S r) halfLineMeasure) {r : ℝ} (hr : 0 < r) :
    (1 + r) * ‖halfLineGreenTail S r‖ ≤
      (∫ rho, ‖S rho‖ ∂halfLineMeasure) + (∫ rho, ‖rho * S rho‖ ∂halfLineMeasure) := by
  have hsub : Ioi r ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hr.le
  have hs : IntegrableOn S (Ioi r) := hS.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hm : IntegrableOn (fun rho => rho * S rho) (Ioi r) := hM.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hn : ‖halfLineGreenTail S r‖ ≤ ∫ rho in Ioi r, ‖S rho‖ := norm_integral_le_integral_norm _
  have h0 : ‖halfLineGreenTail S r‖ ≤ ∫ rho, ‖S rho‖ ∂halfLineMeasure := by
    exact hn.trans (setIntegral_mono_set hS.norm (ae_of_all _ (fun _ => norm_nonneg _)) (Eventually.of_forall fun _ h => hsub h))
  have h1 : r * ‖halfLineGreenTail S r‖ ≤ ∫ rho, ‖rho * S rho‖ ∂halfLineMeasure := by
    calc
      _ ≤ r * ∫ rho in Ioi r, ‖S rho‖ := mul_le_mul_of_nonneg_left hn hr.le
      _ = ∫ rho in Ioi r, r * ‖S rho‖ := (integral_const_mul _ _).symm
      _ ≤ ∫ rho in Ioi r, ‖rho * S rho‖ := by
        apply integral_mono_ae (hs.norm.const_mul r) hm.norm
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        rw [norm_mul, Real.norm_of_nonneg (hr.le.trans hrho.le)]
        exact mul_le_mul_of_nonneg_right hrho.le (norm_nonneg _)
      _ ≤ _ := setIntegral_mono_set hM.norm (ae_of_all _ (fun _ => norm_nonneg _))
        (Eventually.of_forall fun _ h => hsub h)
  nlinarith
end HBL.Modulation.Monopole
