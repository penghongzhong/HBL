import HBL.KinematicPhysicalTimeInverse

/-! A total inverse of the actual remaining physical time and its terminal limit. -/

noncomputable section
open Set Filter
open scoped Topology

namespace HBL.Kinematic

/-- The inverse clock on its actual range, with the initial time as a total fallback. -/
def sliceTimeInverse (A s₀ κ Λ : ℝ) (h : ℝ → ℝ) (u : ℝ) : ℝ := by
  classical
  exact if hs : ∃ s : ℝ, s₀ ≤ s ∧ slicePhysicalTime A s₀ κ Λ h s = u
    then Classical.choose hs else s₀

theorem sliceTimeInverse_spec_of_path
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    {u : ℝ} (hu : 0 < u) (hu₀ : u ≤ slicePhysicalTime A s₀ κ Λ h s₀) :
    s₀ ≤ sliceTimeInverse A s₀ κ Λ h u ∧
      slicePhysicalTime A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u) = u := by
  classical
  have hex := (slicePhysicalTime_existsUnique_of_path h hA hs₀ hδ hδ1 hH hΛ
    hh hbound hsmall hκ hu hu₀).exists
  simpa only [sliceTimeInverse, dite_eq_left hex] using Classical.choose_spec hex

/-- Positive remaining physical time tending to zero forces the actual inverse
clock to tend to infinity; this limit is proved from the original path data. -/
theorem sliceTimeInverse_tendsto_atTop_of_path
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    Tendsto (sliceTimeInverse A s₀ κ Λ h) (𝓝[>] (0 : ℝ)) atTop := by
  have hpos : ∀ s : ℝ, s₀ ≤ s → 0 < slicePhysicalTime A s₀ κ Λ h s := by
    intro s hs
    have hq : 0 < sliceClock A s₀ κ h s :=
      (mul_pos (show 0 < A / 2 by positivity) (hs₀.trans_le hs)).trans_le
        (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
    exact div_pos hq (sq_pos_of_pos (sliceLambda_pos hA (hs₀.trans_le hs) hΛ hq))
  have hm := (slicePhysicalTime_continuousOn_strictAntiOn_of_path h hA hs₀ hδ
    hδ1 hH hΛ hh hbound hsmall hκ).2
  apply tendsto_atTop.2
  intro S
  let R := max s₀ S
  have hR : s₀ ≤ R := le_max_left _ _
  have heRn : ∀ᶠ u in 𝓝 (0 : ℝ), u < slicePhysicalTime A s₀ κ Λ h R :=
    isOpen_Iio.mem_nhds (hpos R hR)
  have he₀n : ∀ᶠ u in 𝓝 (0 : ℝ), u < slicePhysicalTime A s₀ κ Λ h s₀ :=
    isOpen_Iio.mem_nhds (hpos s₀ le_rfl)
  have heR := heRn.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have he₀ := he₀n.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  filter_upwards [self_mem_nhdsWithin, heR, he₀] with u hu huR hu₀
  have hs := sliceTimeInverse_spec_of_path h hA hs₀ hδ hδ1 hH hΛ hh
    hbound hsmall hκ hu hu₀.le
  have hlarge : R < sliceTimeInverse A s₀ κ Λ h u := by
    by_contra hle
    have htime := hm.antitoneOn hs.1 hR (le_of_not_gt hle)
    rw [hs.2] at htime
    exact (not_le_of_gt huR) htime
  exact (le_max_right s₀ S).trans hlarge.le

end HBL.Kinematic
