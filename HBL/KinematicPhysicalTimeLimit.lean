import HBL.KinematicSynchronizedSliceCertified

/-!
Finite terminal physical time for the actual reconstructed clock.
All positivity and integrability conditions in the tail argument are
derived from the same continuous-path decay hypotheses as synchronization.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

theorem sliceReferenceTime_eq_power
    {A Λ s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    sliceReferenceTime A Λ s = (A / Λ ^ 2) * s ^ (-A⁻¹) := by
  have hexp : 1 - sliceBeta A * 2 = -A⁻¹ := by
    unfold sliceBeta
    field_simp
    ring
  have hpow : s ^ (sliceBeta A * 2) = (s ^ sliceBeta A) ^ 2 := by
    simpa using Real.rpow_mul_natCast hs.le (sliceBeta A) 2
  calc
    sliceReferenceTime A Λ s =
        (A / Λ ^ 2) * (s / (s ^ sliceBeta A) ^ 2) := by
      simp only [sliceReferenceTime, mul_pow, div_eq_mul_inv, mul_inv]
      ring
    _ = (A / Λ ^ 2) * s ^ (1 - sliceBeta A * 2) := by
      rw [Real.rpow_sub hs, Real.rpow_one, hpow]
    _ = _ := by rw [hexp]

theorem sliceReferenceTime_tendsto_zero
    {A Λ : ℝ} (hA : 0 < A) :
    Tendsto (sliceReferenceTime A Λ) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop (inv_pos.mpr hA)).const_mul (A / Λ ^ 2)
  simp only [mul_zero] at hp
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (sliceReferenceTime_eq_power hA hs).symm

/-- The reconstructed positive remaining physical time tends to zero,
without assuming a tail limit or any integrability statement. -/
theorem slicePhysicalTime_tendsto_zero_of_path
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    Tendsto (slicePhysicalTime A s₀ κ Λ h) atTop (𝓝 0) := by
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have ht := sliceTailFrom_tendsto_zero h hint
  have hexp : Tendsto (fun s => Real.exp (sliceTailFrom A s₀ κ h s))
      atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using
      (Real.continuous_exp.tendsto (0 : ℝ)).comp ht
  have hprod := (sliceReferenceTime_tendsto_zero (Λ := Λ) hA).mul hexp
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hspos : 0 < s := hs₀.trans_le hs
  have hq : 0 < sliceClock A s₀ κ h s :=
    (mul_pos (show 0 < A / 2 by positivity) hspos).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
  exact (slicePhysicalTime_eq_reference_mul_exp hA hspos hΛ hq).symm

end HBL.Kinematic
