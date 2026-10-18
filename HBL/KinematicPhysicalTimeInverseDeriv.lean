import HBL.KinematicPhysicalTimeInverseMap
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Differentiability of the actual inverse physical clock on its open range. -/

noncomputable section
open Set Filter
open scoped Topology

namespace HBL.Kinematic

/-- The actual inverse clock has derivative minus the square of the actual
scale. Its continuity and inverse identities are proved from the path data. -/
theorem sliceTimeInverse_hasDerivAt_of_path
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    {u : ℝ} (hu : 0 < u) (hu₀ : u < slicePhysicalTime A s₀ κ Λ h s₀) :
    HasDerivAt (sliceTimeInverse A s₀ κ Λ h)
      (-(sliceLambda A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u) ^ 2)) u := by
  have hs := sliceTimeInverse_spec_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound
    hsmall hκ hu hu₀.le
  have hm := (slicePhysicalTime_continuousOn_strictAntiOn_of_path h hA hs₀ hδ
    hδ1 hH hΛ hh hbound hsmall hκ).2
  have hev : ∀ᶠ v in 𝓝 u, s₀ ≤ sliceTimeInverse A s₀ κ Λ h v ∧
      slicePhysicalTime A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h v) = v := by
    filter_upwards [Ioo_mem_nhds hu hu₀] with v hv
    exact sliceTimeInverse_spec_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound
      hsmall hκ hv.1 hv.2.le
  have hslt : s₀ < sliceTimeInverse A s₀ κ Λ h u := by
    by_contra hle
    have heq := le_antisymm (le_of_not_gt hle) hs.1
    have ht := hs.2
    rw [heq] at ht
    exact (ne_of_lt hu₀) ht.symm
  have hcont : ContinuousAt (sliceTimeInverse A s₀ κ Λ h) u := by
    apply tendsto_order.2
    constructor
    · intro b hb
      by_cases hb₀ : b < s₀
      · exact hev.mono (fun _ hv => hb₀.trans_le hv.1)
      · have hb₀ : s₀ ≤ b := le_of_not_gt hb₀
        have htb : u < slicePhysicalTime A s₀ κ Λ h b := by
          rw [← hs.2]
          exact hm hb₀ hs.1 hb
        filter_upwards [hev, Iio_mem_nhds htb] with v hv hvb
        by_contra hle
        have ht := hm.antitoneOn hv.1 hb₀ (le_of_not_gt hle)
        rw [hv.2] at ht
        exact (not_le_of_gt hvb) ht
    · intro b hb
      have hb₀ : s₀ ≤ b := hs.1.trans hb.le
      have htb : slicePhysicalTime A s₀ κ Λ h b < u := by
        rw [← hs.2]
        exact hm hs.1 hb₀ hb
      filter_upwards [hev, Ioi_mem_nhds htb] with v hv hvb
      by_contra hle
      have ht := hm.antitoneOn hb₀ hv.1 (le_of_not_gt hle)
      rw [hv.2] at ht
      exact (not_le_of_gt hvb) ht
  have hd := ((slice_kinematics_of_path h hA hs₀ hδ hδ1 hH hΛ hh
    hbound hsmall hκ).2.1 _ hslt).2.2
  have hq : 0 < sliceClock A s₀ κ h (sliceTimeInverse A s₀ κ Λ h u) :=
    (mul_pos (show 0 < A / 2 by positivity) (hs₀.trans hslt)).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs.1).1
  have hl := sliceLambda_pos hA (hs₀.trans hslt) hΛ hq
  have hn : -(sliceLambda A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u) ^ 2)⁻¹ ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero (sq_pos_of_pos hl).ne')
  simpa only [inv_neg, inv_inv] using
    hd.of_local_left_inverse hcont hn (hev.mono (fun _ hv => hv.2))

end HBL.Kinematic
