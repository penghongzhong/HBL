import HBL.KinematicPhysicalRate
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Conversion of the actual path's renormalized-time error to a physical-time power. -/

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace HBL.Kinematic

/-- The actual physical clock controls the renormalized power error, with no
assumed clock asymptotic or inverse-time estimate. -/
theorem rpow_neg_isBigO_slicePhysicalTime_rpow
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun s : ℝ => s ^ (-δ)) =O[atTop]
      (fun s : ℝ => slicePhysicalTime A s₀ κ Λ h s ^ (A * δ)) := by
  have hB : 0 < A / Λ ^ 2 := div_pos hA (sq_pos_of_pos hΛ)
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have ht := sliceTailFrom_tendsto_zero h hint
  have he : Tendsto (fun s => Real.exp (sliceTailFrom A s₀ κ h s))
      atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using
      (Real.continuous_exp.tendsto (0 : ℝ)).comp ht
  have hp := (he.const_mul (A / Λ ^ 2)).rpow_const (p := -(A * δ))
    (Or.inl (by simpa only [mul_one] using hB.ne'))
  simp only [mul_one] at hp
  have hlim : Tendsto (fun s : ℝ => s ^ (-δ) /
      slicePhysicalTime A s₀ κ Λ h s ^ (A * δ)) atTop
      (𝓝 ((A / Λ ^ 2) ^ (-(A * δ)))) := by
    apply hp.congr'
    filter_upwards [eventually_ge_atTop s₀] with s hs
    have hspos : 0 < s := hs₀.trans_le hs
    have hq : 0 < sliceClock A s₀ κ h s :=
      (mul_pos (show 0 < A / 2 by positivity) hspos).trans_le
        (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
    rw [slicePhysicalTime_eq_reference_mul_exp hA hspos hΛ hq,
      sliceReferenceTime_eq_power hA hspos]
    have hr : (-A⁻¹) * (A * δ) = -δ := by field_simp
    have hsnonzero : s ^ (-δ) ≠ 0 := (Real.rpow_pos_of_pos hspos _).ne'
    rw [Real.mul_rpow (mul_nonneg hB.le (Real.rpow_nonneg hspos.le _))
      (Real.exp_pos _).le, Real.mul_rpow hB.le (Real.rpow_nonneg hspos.le _),
      ← Real.rpow_mul hspos.le, hr,
      Real.rpow_neg (mul_nonneg hB.le (Real.exp_pos _).le),
      Real.mul_rpow hB.le (Real.exp_pos _).le]
    field_simp
  have hc : (A / Λ ^ 2) ^ (-(A * δ)) ≠ 0 := (Real.rpow_pos_of_pos hB _).ne'
  exact isBigO_of_div_tendsto_nhds_of_ne_zero
    (by simpa only [inv_div] using hlim.inv₀ hc) (inv_ne_zero hc)

end HBL.Kinematic
