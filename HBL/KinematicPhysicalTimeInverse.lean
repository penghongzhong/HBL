import HBL.KinematicPhysicalRateError
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! The actual remaining physical time parametrizes its full positive interval. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

theorem slicePhysicalTime_continuousOn_strictAntiOn_of_path
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    ContinuousOn (slicePhysicalTime A s₀ κ Λ h) (Ici s₀) ∧
      StrictAntiOn (slicePhysicalTime A s₀ κ Λ h) (Ici s₀) := by
  have hq : ∀ s : ℝ, s₀ ≤ s → 0 < sliceClock A s₀ κ h s := by
    intro s hs
    exact (mul_pos (show 0 < A / 2 by positivity) (hs₀.trans_le hs)).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have hi := sliceIntegrand_continuousOn h hA hs₀ hh hq
  have hp := clockPerturbation_continuousOn s₀ (sliceIntegrand A s₀ κ h) hi
  have hF : ContinuousOn (sliceTailFrom A s₀ κ h) (Ici s₀) := by
    have hconst : ContinuousOn (fun _ : ℝ => sliceTail A s₀ κ h) (Ici s₀) :=
      continuousOn_const
    apply (hconst.sub (hp.div_const 4)).congr
    intro s hs
    rw [sliceTailFrom_eq_total_sub_interval h hint hs]
    simp only [clockPerturbation, Pi.sub_apply]
    ring
  have hpow : ContinuousOn (fun s : ℝ => s ^ (-A⁻¹)) (Ici s₀) :=
    continuousOn_id.rpow_const (fun s hs => Or.inl (hs₀.trans_le hs).ne')
  have hc : ContinuousOn (slicePhysicalTime A s₀ κ Λ h) (Ici s₀) := by
    apply ((hpow.const_mul (A / Λ ^ 2)).mul
      (Real.continuous_exp.comp_continuousOn hF)).congr
    intro s hs
    rw [slicePhysicalTime_eq_reference_mul_exp hA (hs₀.trans_le hs) hΛ (hq s hs),
      sliceReferenceTime_eq_power hA (hs₀.trans_le hs)]
    rfl
  refine ⟨hc, strictAntiOn_of_deriv_neg (convex_Ici s₀) hc ?_⟩
  intro s hs
  rw [interior_Ici] at hs
  rw [(slicePhysicalTime_hasDerivAt h hA hs₀ hΛ hh hq hint hs).deriv]
  have hl := sliceLambda_pos hA (hs₀.trans hs) hΛ (hq s hs.le)
  exact neg_neg_of_pos (inv_pos.mpr (sq_pos_of_pos hl))

/-- Every positive remaining physical time up to the actual initial value has
exactly one renormalized time in the original half-line. -/
theorem slicePhysicalTime_existsUnique_of_path
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    {u : ℝ} (hu : 0 < u) (hu₀ : u ≤ slicePhysicalTime A s₀ κ Λ h s₀) :
    ∃! s : ℝ, s₀ ≤ s ∧ slicePhysicalTime A s₀ κ Λ h s = u := by
  obtain ⟨hc, hm⟩ := slicePhysicalTime_continuousOn_strictAntiOn_of_path
    h hA hs₀ hδ hδ1 hH hΛ hh hbound hsmall hκ
  have ht := slicePhysicalTime_tendsto_zero_of_path h hA hs₀ hδ hδ1 hH hΛ hh
    hbound hsmall hκ
  have he : ∀ᶠ s in atTop, slicePhysicalTime A s₀ κ Λ h s < u :=
    ht.eventually (isOpen_Iio.mem_nhds hu)
  obtain ⟨b, hb₀, hb⟩ := ((eventually_ge_atTop s₀).and he).exists
  obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc' hb₀
    (hc.mono (fun _ hx => hx.1)) ⟨hb.le, hu₀⟩
  refine ⟨s, ⟨hs.1, hsu⟩, ?_⟩
  intro t ht
  exact hm.injOn ht.1 hs.1 (ht.2.trans hsu.symm)

end HBL.Kinematic
