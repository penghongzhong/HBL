import HBL.KinematicSliceDefinitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Bounds for the actual integrated parameter path, without a prior bound on
the clock perturbation.  The power integral supplies the precise constant
needed in the reciprocal-tail argument.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

theorem clockPerturbation_continuousOn
    (s₀ : ℝ) (h : ℝ → ℝ) (hh : ContinuousOn h (Ici s₀)) :
    ContinuousOn (clockPerturbation s₀ h) (Ici s₀) := by
  let hExt : ℝ → ℝ := fun x => h (max s₀ x)
  have hExtCont : Continuous hExt :=
    hh.comp_continuous (continuous_const.max continuous_id)
      (fun x => le_max_left s₀ x)
  have hprimitive : Continuous (fun s => ∫ x in s₀..s, hExt x) :=
    intervalIntegral.continuous_primitive
      (fun a b => hExtCont.intervalIntegrable a b) s₀
  refine (hprimitive.const_mul 4).continuousOn.congr ?_
  intro s hs
  change 4 * (∫ x in s₀..s, h x) = 4 * (∫ x in s₀..s, hExt x)
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hs] at hx
  simp only [hExt, max_eq_right hx.1]

theorem sliceClock_continuousOn
    (A s₀ κ : ℝ) (h : ℝ → ℝ) (hh : ContinuousOn h (Ici s₀)) :
    ContinuousOn (sliceClock A s₀ κ h) (Ici s₀) := by
  exact ((continuous_const.mul continuous_id).add continuous_const).continuousOn.add
    (clockPerturbation_continuousOn s₀ h hh)

theorem clockPerturbation_abs_le
    {s₀ δ H s : ℝ} (h : ℝ → ℝ)
    (hs₀ : 0 < s₀) (hδ : δ < 1) (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ))
    (hs : s₀ ≤ s) :
    |clockPerturbation s₀ h s| ≤
      4 * H / (1 - δ) * s ^ (1 - δ) := by
  have hexp : -1 < -δ := by linarith
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-δ)) volume s₀ s :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  have hint : |∫ t in s₀..s, h t| ≤
      H * ((s ^ (1 - δ) - s₀ ^ (1 - δ)) / (1 - δ)) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le hs
      (Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hbound t ht.1.le)) (hpow.const_mul H)
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl hexp)] at hi
    simpa only [Real.norm_eq_abs, show -δ + 1 = 1 - δ by ring] using hi
  have hcoef : 0 ≤ 4 * H / (1 - δ) := by positivity
  have hstart : 0 ≤ s₀ ^ (1 - δ) := Real.rpow_nonneg hs₀.le _
  calc
    |clockPerturbation s₀ h s| = 4 * |∫ t in s₀..s, h t| := by
      simp only [clockPerturbation, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    _ ≤ 4 * (H * ((s ^ (1 - δ) - s₀ ^ (1 - δ)) / (1 - δ))) :=
      mul_le_mul_of_nonneg_left hint (by norm_num)
    _ = (4 * H / (1 - δ)) * (s ^ (1 - δ) - s₀ ^ (1 - δ)) := by ring
    _ ≤ 4 * H / (1 - δ) * s ^ (1 - δ) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hstart) hcoef

theorem clockPerturbation_sub
    (s₀ : ℝ) (h k : ℝ → ℝ)
    (hh : ContinuousOn h (Ici s₀)) (hk : ContinuousOn k (Ici s₀))
    {s : ℝ} (hs : s₀ ≤ s) :
    clockPerturbation s₀ h s - clockPerturbation s₀ k s =
      clockPerturbation s₀ (fun t => h t - k t) s := by
  have hhi : IntervalIntegrable h volume s₀ s :=
    (hh.mono (fun _ hx => hx.1)).intervalIntegrable_of_Icc hs
  have hki : IntervalIntegrable k volume s₀ s :=
    (hk.mono (fun _ hx => hx.1)).intervalIntegrable_of_Icc hs
  simp only [clockPerturbation, intervalIntegral.integral_sub hhi hki]
  ring

theorem clockPerturbation_sub_abs_le
    {s₀ δ H s : ℝ} (h k : ℝ → ℝ)
    (hh : ContinuousOn h (Ici s₀)) (hk : ContinuousOn k (Ici s₀))
    (hs₀ : 0 < s₀) (hδ : δ < 1) (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t - k t| ≤ H * t ^ (-δ))
    (hs : s₀ ≤ s) :
    |clockPerturbation s₀ h s - clockPerturbation s₀ k s| ≤
      4 * H / (1 - δ) * s ^ (1 - δ) := by
  rw [clockPerturbation_sub s₀ h k hh hk hs]
  exact clockPerturbation_abs_le (fun t => h t - k t) hs₀ hδ hH hbound hs

theorem clockPerturbation_abs_le_linear
    {s₀ δ H s : ℝ} (h : ℝ → ℝ)
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1) (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ))
    (hs : s₀ ≤ s) :
    |clockPerturbation s₀ h s| ≤
      (4 * H / (1 - δ)) * s₀ ^ (-δ) * s := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hcoef : 0 ≤ 4 * H / (1 - δ) := by positivity
  have hpow : s ^ (-δ) ≤ s₀ ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hs₀ hs (by linarith)
  calc
    |clockPerturbation s₀ h s| ≤ 4 * H / (1 - δ) * s ^ (1 - δ) :=
      clockPerturbation_abs_le h hs₀ hδ1 hH hbound hs
    _ = (4 * H / (1 - δ)) * s ^ (-δ) * s := by
      rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add_one hspos.ne']
      ring
    _ ≤ (4 * H / (1 - δ)) * s₀ ^ (-δ) * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoef) hspos.le

theorem sliceClock_linear_bounds
    {A s₀ κ δ H s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) (hs : s₀ ≤ s) :
    A / 2 * s ≤ sliceClock A s₀ κ h s ∧
      sliceClock A s₀ κ h s ≤ 2 * A * s := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hp : |clockPerturbation s₀ h s| ≤ A / 4 * s :=
    (clockPerturbation_abs_le_linear h hs₀ hδ hδ1 hH hbound hs).trans
      (mul_le_mul_of_nonneg_right hsmall hspos.le)
  have hk : |κ| ≤ A / 4 * s := by
    calc
      |κ| ≤ A * s₀ / 4 := hκ
      _ ≤ A / 4 * s := by nlinarith
  have hp' := abs_le.mp hp
  have hk' := abs_le.mp hk
  unfold sliceClock
  constructor <;> nlinarith [mul_nonneg hA.le hspos.le]

theorem clockPerturbation_div_self_tendsto_zero
    {s₀ δ H : ℝ} (h : ℝ → ℝ)
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1) (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ)) :
    Tendsto (fun s : ℝ => clockPerturbation s₀ h s / s) atTop (𝓝 0) := by
  have hlim : Tendsto (fun s : ℝ => (4 * H / (1 - δ)) * s ^ (-δ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop hδ).const_mul (4 * H / (1 - δ))
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hspos : 0 < s := hs₀.trans_le hs
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hspos]
  calc
    |clockPerturbation s₀ h s| / s ≤
        (4 * H / (1 - δ) * s ^ (1 - δ)) / s :=
      div_le_div_of_nonneg_right
        (clockPerturbation_abs_le h hs₀ hδ1 hH hbound hs) hspos.le
    _ = (4 * H / (1 - δ)) * s ^ (-δ) := by
      rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add_one hspos.ne']
      field_simp

theorem sliceClock_div_affine_tendsto_one
    {A s₀ κ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ)) :
    Tendsto (fun s : ℝ => sliceClock A s₀ κ h s / (A * s)) atTop (𝓝 1) := by
  have hp := clockPerturbation_div_self_tendsto_zero h hs₀ hδ hδ1 hH hbound
  have hk : Tendsto (fun s : ℝ => κ / s) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul κ
  have ht : Tendsto
      (fun s : ℝ => 1 + (κ / s + clockPerturbation s₀ h s / s) / A)
      atTop (𝓝 1) := by
    simpa only [add_zero, zero_div] using ((hk.add hp).div_const A).const_add 1
  apply ht.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with s hs
  unfold sliceClock
  field_simp [hA.ne', hs]
  ring

end HBL.Kinematic
