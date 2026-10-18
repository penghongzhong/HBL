import HBL.KinematicPhysicalTimeInverseDeriv
import HBL.KinematicPhysicalTimeAsymptotics
import HBL.KinematicPhaseDynamics

/-! Differential equations for the actual scale and phase in physical time. -/

noncomputable section
open Set Filter
open scoped Topology
namespace HBL.Kinematic

private theorem inverse_dynamics_data
    {A s₀ κ δ H Λ u : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    (hu : 0 < u) (hu₀ : u < slicePhysicalTime A s₀ κ Λ h s₀) :
    s₀ < sliceTimeInverse A s₀ κ Λ h u ∧
      sliceLambda A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u) ^ 2 /
        sliceClock A s₀ κ h (sliceTimeInverse A s₀ κ Λ h u) = u⁻¹ := by
  have hs := sliceTimeInverse_spec_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound
    hsmall hκ hu hu₀.le
  constructor
  · by_contra hn
    have he := le_antisymm (le_of_not_gt hn) hs.1
    have ht := hs.2
    rw [he] at ht
    linarith
  · simpa only [slicePhysicalTime, inv_div] using congrArg Inv.inv hs.2

/-- The actual remaining-time phase equation, obtained from the original phase tail. -/
theorem physicalSliceGamma_hasDerivAt
    {A s₀ κ δ H J Λ θ γ u : ℝ} (h g : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hg : ContinuousOn g (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (gbound : ∀ s : ℝ, s₀ ≤ s → |g s| ≤ J * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    (hu : 0 < u) (hu₀ : u < slicePhysicalTime A s₀ κ Λ h s₀) :
    HasDerivAt (physicalSliceGamma A s₀ κ Λ θ γ h g)
      ((θ + g (sliceTimeInverse A s₀ κ Λ h u)) / u) u := by
  obtain ⟨hs, hr⟩ := inverse_dynamics_data h hA hs₀ hδ hδ1 hH hΛ hh hbound hsmall hκ hu hu₀
  have hd := sliceGamma_hasDerivAt_of_path (θ := θ) (γ := γ) h g hA hs₀ hδ hδ1
    hH hh hg hbound gbound hsmall hκ hs
  have hi := sliceTimeInverse_hasDerivAt_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound
    hsmall hκ hu hu₀
  apply (hd.comp u hi).congr_deriv
  calc
    _ = (θ + g (sliceTimeInverse A s₀ κ Λ h u)) *
        (sliceLambda A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u) ^ 2 /
          sliceClock A s₀ κ h (sliceTimeInverse A s₀ κ Λ h u)) := by ring
    _ = _ := by rw [hr]; rfl

/-- The phase equation in the original time variable `t`, with `u = T - t`. -/
theorem physicalSliceGamma_hasDerivAt_time
    {A s₀ κ δ H J Λ θ γ T t : ℝ} (h g : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hg : ContinuousOn g (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (gbound : ∀ s : ℝ, s₀ ≤ s → |g s| ≤ J * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    (ht : t < T) (ht₀ : T - t < slicePhysicalTime A s₀ κ Λ h s₀) :
    HasDerivAt (fun v => physicalSliceGamma A s₀ κ Λ θ γ h g (T - v))
      (-(θ + g (sliceTimeInverse A s₀ κ Λ h (T - t))) / (T - t)) t := by
  have hd := physicalSliceGamma_hasDerivAt (θ := θ) (γ := γ) h g hA hs₀ hδ hδ1
    hH hΛ hh hg hbound gbound hsmall hκ (sub_pos.mpr ht) ht₀
  apply (hd.comp t ((hasDerivAt_id t).const_sub T)).congr_deriv
  ring

/-- The logarithmic scale equation in positive remaining physical time. -/
theorem physicalSliceLambda_log_hasDerivAt
    {A s₀ κ δ H Λ u : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    (hu : 0 < u) (hu₀ : u < slicePhysicalTime A s₀ κ Λ h s₀) :
    HasDerivAt (fun v => Real.log (physicalSliceLambda A s₀ κ Λ h v))
      (-(A + 4 * h (sliceTimeInverse A s₀ κ Λ h u) + 1) / (2 * u)) u := by
  obtain ⟨hs, hr⟩ := inverse_dynamics_data h hA hs₀ hδ hδ1 hH hΛ hh hbound hsmall hκ hu hu₀
  have hq : ∀ s : ℝ, s₀ ≤ s → 0 < sliceClock A s₀ κ h s := by
    intro s hs
    exact (mul_pos (show 0 < A / 2 by positivity) (hs₀.trans_le hs)).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have hd := sliceLambda_log_hasDerivAt h hA hs₀ hΛ hh hq hint hs
  have hi := sliceTimeInverse_hasDerivAt_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound
    hsmall hκ hu hu₀
  apply (hd.comp u hi).congr_deriv
  calc
    _ = -(A + 4 * h (sliceTimeInverse A s₀ κ Λ h u) + 1) / 2 *
        (sliceLambda A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u) ^ 2 /
          sliceClock A s₀ κ h (sliceTimeInverse A s₀ κ Λ h u)) := by ring
    _ = _ := by rw [hr]; ring

/-- The scale equation in positive remaining physical time. -/
private theorem physicalSliceLambda_hasDerivAt
    {A s₀ κ δ H Λ u : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    (hu : 0 < u) (hu₀ : u < slicePhysicalTime A s₀ κ Λ h s₀) :
    HasDerivAt (physicalSliceLambda A s₀ κ Λ h)
      (-(A + 4 * h (sliceTimeInverse A s₀ κ Λ h u) + 1) / (2 * u) *
        physicalSliceLambda A s₀ κ Λ h u) u := by
  obtain ⟨hs, hr⟩ := inverse_dynamics_data h hA hs₀ hδ hδ1 hH hΛ hh hbound hsmall hκ hu hu₀
  have hq : ∀ s : ℝ, s₀ ≤ s → 0 < sliceClock A s₀ κ h s := by
    intro s hs
    exact (mul_pos (show 0 < A / 2 by positivity) (hs₀.trans_le hs)).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have hd := sliceLambda_hasDerivAt h hA hs₀ hΛ hh hq hint hs
  have hi := sliceTimeInverse_hasDerivAt_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound
    hsmall hκ hu hu₀
  apply (hd.comp u hi).congr_deriv
  calc
    _ = -(A + 4 * h (sliceTimeInverse A s₀ κ Λ h u) + 1) / 2 *
        (sliceLambda A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u) ^ 2 /
          sliceClock A s₀ κ h (sliceTimeInverse A s₀ κ Λ h u)) *
        physicalSliceLambda A s₀ κ Λ h u := by unfold physicalSliceLambda; ring
    _ = _ := by rw [hr]; ring

/-- The scale equation in the original physical time. -/
theorem physicalSliceLambda_hasDerivAt_time
    {A s₀ κ δ H Λ T t : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4)
    (ht : t < T) (ht₀ : T - t < slicePhysicalTime A s₀ κ Λ h s₀) :
    HasDerivAt (fun v => physicalSliceLambda A s₀ κ Λ h (T - v))
      ((A + 4 * h (sliceTimeInverse A s₀ κ Λ h (T - t)) + 1) / (2 * (T - t)) *
        physicalSliceLambda A s₀ κ Λ h (T - t)) t := by
  have hd := physicalSliceLambda_hasDerivAt h hA hs₀ hδ hδ1 hH hΛ hh hbound
    hsmall hκ (sub_pos.mpr ht) ht₀
  apply (hd.comp t ((hasDerivAt_id t).const_sub T)).congr_deriv
  ring

end HBL.Kinematic
