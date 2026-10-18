import HBL.KinematicPhysicalRate
import HBL.KinematicRateInputBounds
import HBL.KinematicRateSmoothTransfer
import HBL.KinematicPhysicalTimePower

/-!
The normalized physical-rate error in terms of the actual clock ratio and
the convergent reciprocal tail. Its quantitative bound uses only the same
continuous-path decay conditions as the synchronized slice.
-/

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace HBL.Kinematic

/-- The rate error has a direct scalar formula with no inverse-clock step. -/
theorem slice_physical_rate_ratio_eq
    {A s₀ κ Λ s : ℝ} {h : ℝ → ℝ}
    (hA : 0 < A) (hs : 0 < s) (hΛ : 0 < Λ)
    (hq : 0 < sliceClock A s₀ κ h s) :
    (sliceLambda A s₀ κ Λ h s)⁻¹ /
        ((Λ ^ A * A ^ (-((A + 1) / 2))) *
          slicePhysicalTime A s₀ κ Λ h s ^ ((A + 1) / 2)) =
      (sliceClock A s₀ κ h s / (A * s)) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(A / 2) * sliceTailFrom A s₀ κ h s) := by
  have hl := sliceLambda_pos hA hs hΛ hq
  have hb : 0 < Λ * s ^ sliceBeta A := mul_pos hΛ (Real.rpow_pos_of_pos hs _)
  have hQ : 0 < sliceClock A s₀ κ h s / (A * s) := div_pos hq (mul_pos hA hs)
  have hS := Real.sqrt_pos.mpr hQ
  have hE := Real.exp_pos (-(sliceTailFrom A s₀ κ h s) / 2)
  have hL : sliceLambda A s₀ κ Λ h s / (Λ * s ^ sliceBeta A) =
      Real.sqrt (sliceClock A s₀ κ h s / (A * s)) *
        Real.exp (-(sliceTailFrom A s₀ κ h s) / 2) := by
    unfold sliceLambda
    field_simp
  unfold slicePhysicalTime
  rw [inverseScale_div_physicalRate_eq hA hΛ hs hl hq, hL]
  apply Real.log_injOn_pos
    (by change (0 : ℝ) < _; positivity) (by change (0 : ℝ) < _; positivity)
  rw [Real.log_mul (Real.rpow_pos_of_pos hQ _).ne'
      (Real.rpow_pos_of_pos (mul_pos hS hE) _).ne',
    Real.log_rpow hQ, Real.log_rpow (mul_pos hS hE),
    Real.log_mul hS.ne' hE.ne', Real.log_sqrt hQ.le, Real.log_exp,
    Real.log_mul (Real.rpow_pos_of_pos hQ _).ne' (Real.exp_pos _).ne',
    Real.log_rpow hQ, Real.log_exp]
  ring

/-- Quantitative physical power-law error for the actual reconstructed path.
The positive exponent is `A * δ`; no asymptotic bound on the reconstructed
clock, scale or reciprocal tail is assumed in this terminal theorem. -/
theorem slice_physical_rate_error_isBigO
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun s : ℝ => (sliceLambda A s₀ κ Λ h s)⁻¹ /
      ((Λ ^ A * A ^ (-((A + 1) / 2))) *
        slicePhysicalTime A s₀ κ Λ h s ^ ((A + 1) / 2)) - 1)
      =O[atTop] (fun s : ℝ => slicePhysicalTime A s₀ κ Λ h s ^ (A * δ)) := by
  have hQ := sliceClock_div_affine_tendsto_one (κ := κ) h hA hs₀ hδ hδ1 hH hbound
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have hF := sliceTailFrom_tendsto_zero h hint
  have hQO := sliceClock_div_affine_sub_one_isBigO (κ := κ) h hA hs₀ hδ1 hH hbound
  have hFO := sliceTailFrom_isBigO_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have hfactor := normalizedRateFactor_sub_one_isBigO A hQ hF hQO hFO
  have htime := rpow_neg_isBigO_slicePhysicalTime_rpow h hA hs₀ hδ hδ1 hH hΛ
    hh hbound hsmall hκ
  apply (hfactor.trans htime).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hspos : 0 < s := hs₀.trans_le hs
  have hqpos : 0 < sliceClock A s₀ κ h s :=
    (mul_pos (by positivity : 0 < A / 2) hspos).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
  exact congrArg (fun x : ℝ => x - 1)
    (slice_physical_rate_ratio_eq hA hspos hΛ hqpos).symm

end HBL.Kinematic
