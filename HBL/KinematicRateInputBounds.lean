import HBL.KinematicPhysicalRate

/-!
Quantitative input bounds for the reconstructed physical rate.  The lower
limit of a tail varies while the clock's original base point `s₀` stays fixed.
-/

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology

namespace HBL.Kinematic

theorem sliceClock_div_affine_sub_one_isBigO
    {A s₀ κ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ1 : δ < 1) (hH : 0 ≤ H)
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ)) :
    (fun s : ℝ => sliceClock A s₀ κ h s / (A * s) - 1)
      =O[atTop] (fun s : ℝ => s ^ (-δ)) := by
  apply IsBigO.of_bound ((|κ| + 4 * H / (1 - δ)) / A)
  filter_upwards [eventually_ge_atTop s₀, eventually_ge_atTop (1 : ℝ)] with s hs hs1
  have hspos : 0 < s := hs₀.trans_le hs
  have hp := clockPerturbation_abs_le h hs₀ hδ1 hH hbound hs
  have hid : sliceClock A s₀ κ h s / (A * s) - 1 =
      (κ + clockPerturbation s₀ h s) / (A * s) := by
    unfold sliceClock
    field_simp
    ring
  have hpow : s ^ (1 - δ) / s = s ^ (-δ) := by
    rw [← Real.rpow_sub_one hspos.ne']
    congr 1
    ring
  have hi : s⁻¹ ≤ s ^ (-δ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hspos.le _),
    hid, abs_div, abs_of_pos (mul_pos hA hspos)]
  calc
    |κ + clockPerturbation s₀ h s| / (A * s) ≤
        (|κ| + (4 * H / (1 - δ)) * s ^ (1 - δ)) / (A * s) :=
      div_le_div_of_nonneg_right
        ((abs_add_le _ _).trans (add_le_add le_rfl hp)) (mul_pos hA hspos).le
    _ = (|κ| / A) * s⁻¹ + (4 * H / (1 - δ) / A) * s ^ (-δ) := by
      calc
        _ = (|κ| / A) * s⁻¹ +
            (4 * H / (1 - δ) / A) * (s ^ (1 - δ) / s) := by
          field_simp
        _ = _ := by rw [hpow]
    _ ≤ (|κ| / A) * s ^ (-δ) + (4 * H / (1 - δ) / A) * s ^ (-δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hi (div_nonneg (abs_nonneg _) hA.le)) le_rfl
    _ = _ := by ring

/-- A moving tail lower limit, with the original clock base point unchanged. -/
theorem sliceTailFrom_abs_le_of_path
    {A s₀ κ δ H s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) (hs : s₀ ≤ s) :
    |sliceTailFrom A s₀ κ h s| ≤
      |κ| / ((A / 2) * A) * s⁻¹ +
        (4 * H / (1 - δ) / ((A / 2) * A)) * (s ^ (-δ) / δ) := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hint := (sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ).mono_set
    (Ioi_subset_Ioi hs)
  have hi₂ := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-2 : ℝ) < -1) hspos).const_mul (|κ| / ((A / 2) * A))
  have hiδ := (integrableOn_Ioi_rpow_of_lt (show -1 - δ < -1 by linarith) hspos).const_mul
    (4 * H / (1 - δ) / ((A / 2) * A))
  calc
    |sliceTailFrom A s₀ κ h s| ≤
        ∫ t in Ioi s, |sliceIntegrand A s₀ κ h t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi s,
        (|κ| / ((A / 2) * A)) * t ^ (-2 : ℝ) +
          (4 * H / (1 - δ) / ((A / 2) * A)) * t ^ (-1 - δ) := by
      apply integral_mono_ae hint.abs (hi₂.add hiδ)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht₀ : s₀ ≤ t := hs.trans ht.le
      exact sliceIntegrand_abs_le hA (hspos.trans ht) (show 0 < A / 2 by positivity)
        (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ ht₀).1
        (clockPerturbation_abs_le h hs₀ hδ1 hH hbound ht₀)
    _ = _ := by
      rw [integral_add hi₂ hiδ, integral_const_mul, integral_const_mul,
        integral_Ioi_rpow_neg_two hspos, integral_Ioi_rpow_neg_one_sub hspos hδ]

theorem sliceTailFrom_isBigO_of_path
    {A s₀ κ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    sliceTailFrom A s₀ κ h =O[atTop] (fun s : ℝ => s ^ (-δ)) := by
  apply IsBigO.of_bound
    (|κ| / ((A / 2) * A) + (4 * H / (1 - δ) / ((A / 2) * A)) / δ)
  filter_upwards [eventually_ge_atTop s₀, eventually_ge_atTop (1 : ℝ)] with s hs hs1
  have hspos : 0 < s := hs₀.trans_le hs
  have hi : s⁻¹ ≤ s ^ (-δ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
  calc
    |sliceTailFrom A s₀ κ h s| ≤ |κ| / ((A / 2) * A) * s⁻¹ +
        (4 * H / (1 - δ) / ((A / 2) * A)) * (s ^ (-δ) / δ) :=
      sliceTailFrom_abs_le_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ hs
    _ ≤ |κ| / ((A / 2) * A) * s ^ (-δ) +
        (4 * H / (1 - δ) / ((A / 2) * A)) * (s ^ (-δ) / δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hi (by positivity)) le_rfl
    _ = _ := by ring

end HBL.Kinematic
