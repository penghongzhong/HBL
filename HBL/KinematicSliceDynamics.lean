import HBL.KinematicPathBounds
import HBL.KinematicSliceNormalizationBridge

/-!
The actual differential identities and terminal normalization of the
reciprocal-tail construction.  Positivity and absolute integrability are
explicit domain conditions, supplied by the path-estimate modules.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

theorem clockPerturbation_hasDerivAt
    {s₀ s : ℝ} (h : ℝ → ℝ) (hh : ContinuousOn h (Ici s₀))
    (hs : s₀ < s) :
    HasDerivAt (clockPerturbation s₀ h) (4 * h s) s := by
  have hi : IntervalIntegrable h volume s₀ s :=
    (hh.mono (fun _ hx => hx.1)).intervalIntegrable_of_Icc hs.le
  have hm : StronglyMeasurableAtFilter h (𝓝 s) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hh.mono Ioi_subset_Ici_self) s hs
  have hc : ContinuousAt h s :=
    (hh s hs.le).continuousAt (Ici_mem_nhds hs)
  exact (intervalIntegral.integral_hasDerivAt_right hi hm hc).const_mul 4

theorem sliceClock_hasDerivAt
    {A s₀ κ s : ℝ} (h : ℝ → ℝ) (hh : ContinuousOn h (Ici s₀))
    (hs : s₀ < s) :
    HasDerivAt (sliceClock A s₀ κ h) (A + 4 * h s) s := by
  have hi := clockPerturbation_hasDerivAt h hh hs
  convert (((hasDerivAt_id s).const_mul A).add_const κ).add hi using 1
  · funext x
    simp only [sliceClock, Pi.add_apply, id_eq]
  · simp only [mul_one]

theorem sliceIntegrand_continuousOn
    {A s₀ κ : ℝ} (h : ℝ → ℝ) (hA : 0 < A) (hs₀ : 0 < s₀)
    (hh : ContinuousOn h (Ici s₀))
    (hq : ∀ s : ℝ, s₀ ≤ s → 0 < sliceClock A s₀ κ h s) :
    ContinuousOn (sliceIntegrand A s₀ κ h) (Ici s₀) := by
  have hc := (sliceClock_continuousOn A s₀ κ h hh).inv₀
    (fun s hs => (hq s hs).ne')
  have ha : ContinuousOn (fun s : ℝ => (A * s)⁻¹) (Ici s₀) :=
    (continuous_const.mul continuous_id).continuousOn.inv₀
      (fun s hs => (mul_pos hA (hs₀.trans_le hs)).ne')
  exact hc.sub ha

theorem sliceTailFrom_eq_total_sub_interval
    {A s₀ κ s : ℝ} (h : ℝ → ℝ)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hs : s₀ ≤ s) :
    sliceTailFrom A s₀ κ h s = sliceTail A s₀ κ h -
      ∫ t in s₀..s, sliceIntegrand A s₀ κ h t := by
  have heq := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hs))
  unfold sliceTailFrom sliceTail
  linarith

theorem sliceTailFrom_hasDerivAt
    {A s₀ κ s : ℝ} (h : ℝ → ℝ) (hA : 0 < A) (hs₀ : 0 < s₀)
    (hh : ContinuousOn h (Ici s₀))
    (hq : ∀ t : ℝ, s₀ ≤ t → 0 < sliceClock A s₀ κ h t)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hs : s₀ < s) :
    HasDerivAt (sliceTailFrom A s₀ κ h)
      (-sliceIntegrand A s₀ κ h s) s := by
  have hc := sliceIntegrand_continuousOn h hA hs₀ hh hq
  have hi : IntervalIntegrable (sliceIntegrand A s₀ κ h) volume s₀ s :=
    (hc.mono (fun _ hx => hx.1)).intervalIntegrable_of_Icc hs.le
  have hm : StronglyMeasurableAtFilter (sliceIntegrand A s₀ κ h) (𝓝 s) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hc.mono Ioi_subset_Ici_self) s hs
  have hd := intervalIntegral.integral_hasDerivAt_right hi hm
    ((hc s hs.le).continuousAt (Ici_mem_nhds hs))
  have hmodel : HasDerivAt
      (fun x => sliceTail A s₀ κ h - ∫ t in s₀..x, sliceIntegrand A s₀ κ h t)
      (-sliceIntegrand A s₀ κ h s) s := by
    convert (hasDerivAt_const s (sliceTail A s₀ κ h)).sub hd using 1
    ring
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact sliceTailFrom_eq_total_sub_interval h hint hx.le

theorem sliceTailFrom_tendsto_zero
    {A s₀ κ : ℝ} (h : ℝ → ℝ)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀)) :
    Tendsto (sliceTailFrom A s₀ κ h) atTop (𝓝 0) := by
  have hi := intervalIntegral_tendsto_integral_Ioi s₀ hint
    (tendsto_id : Tendsto (fun s : ℝ => s) atTop atTop)
  have hdiff := hi.const_sub (sliceTail A s₀ κ h)
  simp only [sliceTail, sub_self] at hdiff
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop s₀] with s hs
  exact (sliceTailFrom_eq_total_sub_interval h hint hs).symm

theorem sliceLambda_log_eq
    {A s₀ κ Λ s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs : 0 < s) (hΛ : 0 < Λ)
    (hq : 0 < sliceClock A s₀ κ h s) :
    Real.log (sliceLambda A s₀ κ Λ h s) =
      Real.log Λ + (sliceBeta A - 1 / 2) * Real.log s +
        (Real.log (sliceClock A s₀ κ h s) - Real.log A) / 2 -
          sliceTailFrom A s₀ κ h s / 2 := by
  have hbase : 0 < Λ * s ^ sliceBeta A :=
    mul_pos hΛ (Real.rpow_pos_of_pos hs _)
  have hratio : 0 < sliceClock A s₀ κ h s / (A * s) :=
    div_pos hq (mul_pos hA hs)
  have hsqrt : 0 < Real.sqrt (sliceClock A s₀ κ h s / (A * s)) :=
    Real.sqrt_pos.2 hratio
  unfold sliceLambda
  rw [Real.log_mul (mul_pos hbase hsqrt).ne' (Real.exp_pos _).ne',
    Real.log_mul hbase.ne' hsqrt.ne',
    Real.log_mul hΛ.ne' (Real.rpow_pos_of_pos hs _).ne',
    Real.log_rpow hs, Real.log_sqrt hratio.le,
    Real.log_div hq.ne' (mul_pos hA hs).ne', Real.log_mul hA.ne' hs.ne',
    Real.log_exp]
  ring

theorem sliceLambda_log_hasDerivAt
    {A s₀ κ Λ s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hΛ : 0 < Λ)
    (hh : ContinuousOn h (Ici s₀))
    (hq : ∀ t : ℝ, s₀ ≤ t → 0 < sliceClock A s₀ κ h t)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hs : s₀ < s) :
    HasDerivAt (fun t => Real.log (sliceLambda A s₀ κ Λ h t))
      ((A + 4 * h s + 1) / (2 * sliceClock A s₀ κ h s)) s := by
  have hspos : 0 < s := hs₀.trans hs
  have hdq := (sliceClock_hasDerivAt h hh hs).log (hq s hs.le).ne'
  have hds := Real.hasDerivAt_log hspos.ne'
  have hdt := sliceTailFrom_hasDerivAt h hA hs₀ hh hq hint hs
  have hmodel : HasDerivAt
      (fun t => Real.log Λ + (sliceBeta A - 1 / 2) * Real.log t +
        (Real.log (sliceClock A s₀ κ h t) - Real.log A) / 2 -
          sliceTailFrom A s₀ κ h t / 2)
      ((A + 4 * h s + 1) / (2 * sliceClock A s₀ κ h s)) s := by
    convert (((hasDerivAt_const s (Real.log Λ)).add
      (hds.const_mul (sliceBeta A - 1 / 2))).add
      ((hdq.sub_const (Real.log A)).div_const 2)).sub (hdt.div_const 2) using 1
    unfold sliceBeta sliceIntegrand
    field_simp [hA.ne', hspos.ne', (hq s hs.le).ne']
    ring
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact sliceLambda_log_eq h hA (hs₀.trans ht) hΛ (hq t ht.le)

theorem sliceLambda_hasDerivAt
    {A s₀ κ Λ s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hΛ : 0 < Λ)
    (hh : ContinuousOn h (Ici s₀))
    (hq : ∀ t : ℝ, s₀ ≤ t → 0 < sliceClock A s₀ κ h t)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hs : s₀ < s) :
    HasDerivAt (sliceLambda A s₀ κ Λ h)
      (((A + 4 * h s + 1) / (2 * sliceClock A s₀ κ h s)) *
        sliceLambda A s₀ κ Λ h s) s := by
  have hd := (sliceLambda_log_hasDerivAt h hA hs₀ hΛ hh hq hint hs).exp
  have hpos := sliceLambda_pos hA (hs₀.trans hs) hΛ (hq s hs.le)
  have hmodel : HasDerivAt
      (fun t => Real.exp (Real.log (sliceLambda A s₀ κ Λ h t)))
      (((A + 4 * h s + 1) / (2 * sliceClock A s₀ κ h s)) *
        sliceLambda A s₀ κ Λ h s) s := by
    convert hd using 1
    rw [Real.exp_log hpos]
    ring
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact (Real.exp_log (sliceLambda_pos hA (hs₀.trans ht) hΛ (hq t ht.le))).symm

theorem sliceLambda_div_terminal_tendsto_one
    {A s₀ κ Λ : ℝ} (h : ℝ → ℝ) (hΛ : 0 < Λ)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hratio : Tendsto (fun s : ℝ => sliceClock A s₀ κ h s / (A * s))
      atTop (𝓝 1)) :
    Tendsto (fun s : ℝ => sliceLambda A s₀ κ Λ h s / (Λ * s ^ sliceBeta A))
      atTop (𝓝 1) := by
  have ht := sliceTailFrom_tendsto_zero h hint
  have hsqrt : Tendsto
      (fun s : ℝ => Real.sqrt (sliceClock A s₀ κ h s / (A * s))) atTop (𝓝 1) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hratio using 1 <;>
      norm_num [Function.comp_def]
  have hexp : Tendsto (fun s : ℝ => Real.exp (-sliceTailFrom A s₀ κ h s / 2))
      atTop (𝓝 1) := by
    convert Real.continuous_exp.continuousAt.tendsto.comp (ht.neg.div_const 2) using 1 <;>
      norm_num [Function.comp_def]
  have hprod := hsqrt.mul hexp
  simp only [mul_one] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  unfold sliceLambda
  field_simp [hΛ.ne', (Real.rpow_pos_of_pos hs (sliceBeta A)).ne']

theorem slicePhysicalTime_hasDerivAt
    {A s₀ κ Λ s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hΛ : 0 < Λ)
    (hh : ContinuousOn h (Ici s₀))
    (hq : ∀ t : ℝ, s₀ ≤ t → 0 < sliceClock A s₀ κ h t)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hs : s₀ < s) :
    HasDerivAt (slicePhysicalTime A s₀ κ Λ h)
      (-(sliceLambda A s₀ κ Λ h s ^ 2)⁻¹) s := by
  have hdq := sliceClock_hasDerivAt (A := A) (κ := κ) h hh hs
  have hdl := sliceLambda_hasDerivAt h hA hs₀ hΛ hh hq hint hs
  have hlne : sliceLambda A s₀ κ Λ h s ≠ 0 :=
    (sliceLambda_pos hA (hs₀.trans hs) hΛ (hq s hs.le)).ne'
  convert hdq.div (hdl.pow 2) (pow_ne_zero 2 hlne) using 1
  · funext t
    rfl
  · simp only [Pi.pow_apply]
    field_simp [hlne, (hq s hs.le).ne']
    ring

theorem sliceLambda_div_terminal_tendsto_one_of_path_bound
    {A s₀ κ Λ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hΛ : 0 < Λ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ))
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀)) :
    Tendsto (fun s : ℝ => sliceLambda A s₀ κ Λ h s / (Λ * s ^ sliceBeta A))
      atTop (𝓝 1) := by
  exact sliceLambda_div_terminal_tendsto_one h hΛ hint
    (sliceClock_div_affine_tendsto_one h hA hs₀ hδ hδ1 hH hbound)

end HBL.Kinematic
