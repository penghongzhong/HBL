import HBL.KinematicPhysicalTimeInverseMap
import HBL.KinematicPhysicalPhase
import HBL.KinematicRemainingTime

/-! Actual scale and phase, parametrized by positive remaining physical time. -/

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace HBL.Kinematic

def physicalSliceLambda (A s₀ κ Λ : ℝ) (h : ℝ → ℝ) (u : ℝ) : ℝ :=
  sliceLambda A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u)

def physicalSliceGamma (A s₀ κ Λ θ γ : ℝ) (h g : ℝ → ℝ) (u : ℝ) : ℝ :=
  sliceGamma A s₀ κ θ γ h g (sliceTimeInverse A s₀ κ Λ h u)

private theorem inverse_physicalTime_eventuallyEq
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun u => slicePhysicalTime A s₀ κ Λ h (sliceTimeInverse A s₀ κ Λ h u))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun u => u) := by
  have hq : 0 < sliceClock A s₀ κ h s₀ :=
    (mul_pos (show 0 < A / 2 by positivity) hs₀).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ le_rfl).1
  have hl := sliceLambda_pos hA hs₀ hΛ hq
  have ht : 0 < slicePhysicalTime A s₀ κ Λ h s₀ :=
    div_pos hq (sq_pos_of_pos hl)
  have he : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      u < slicePhysicalTime A s₀ κ Λ h s₀ :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he] with u hu hu₀
  exact (sliceTimeInverse_spec_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound
    hsmall hκ hu hu₀.le).2

/-- The actual inverse parametrization gives the physical power-law error at `u → 0+`.
Only the original path continuity, decay and smallness assumptions are used. -/
theorem physicalSliceLambda_rate_error_isBigO
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun u : ℝ => (physicalSliceLambda A s₀ κ Λ h u)⁻¹ /
      ((Λ ^ A * A ^ (-((A + 1) / 2))) * u ^ ((A + 1) / 2)) - 1)
      =O[𝓝[>] (0 : ℝ)] (fun u : ℝ => u ^ (A * δ)) := by
  have hi := sliceTimeInverse_tendsto_atTop_of_path h hA hs₀ hδ hδ1 hH hΛ
    hh hbound hsmall hκ
  have hb := (slice_physical_rate_error_isBigO h hA hs₀ hδ hδ1 hH hΛ hh
    hbound hsmall hκ).comp_tendsto hi
  have he := inverse_physicalTime_eventuallyEq h hA hs₀ hδ hδ1 hH hΛ hh
    hbound hsmall hκ
  apply hb.congr' ?_ ?_
  · filter_upwards [he] with u hu
    simp only [Function.comp_apply, physicalSliceLambda, hu]
  · filter_upwards [he] with u hu
    simp only [Function.comp_apply, hu]

/-- The original phase integral has a quantitative logarithmic expansion at `u → 0+`. -/
theorem physicalSliceGamma_log_error_isBigO
    {A s₀ κ δ H J Λ θ γ : ℝ} (h g : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hg : ContinuousOn g (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (gbound : ∀ s : ℝ, s₀ ≤ s → |g s| ≤ J * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun u : ℝ => physicalSliceGamma A s₀ κ Λ θ γ h g u - θ * Real.log u -
      (γ - θ * Real.log (A / Λ ^ 2)))
      =O[𝓝[>] (0 : ℝ)] (fun u : ℝ => u ^ (A * δ)) := by
  have hi := sliceTimeInverse_tendsto_atTop_of_path h hA hs₀ hδ hδ1 hH hΛ
    hh hbound hsmall hκ
  have hb := (sliceGamma_physical_error_isBigO (θ := θ) (γ := γ) h g hA hs₀ hδ hδ1 hH hΛ hh hg
    hbound gbound hsmall hκ).comp_tendsto hi
  have he := inverse_physicalTime_eventuallyEq h hA hs₀ hδ hδ1 hH hΛ hh
    hbound hsmall hκ
  apply hb.congr' ?_ ?_
  · filter_upwards [he] with u hu
    simp only [Function.comp_apply, physicalSliceGamma, hu]
  · filter_upwards [he] with u hu
    simp only [Function.comp_apply, hu]

/-- The scale law in the original physical time, approaching the terminal time from below. -/
theorem physicalSliceLambda_rate_error_at_terminal
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ) (T : ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun t : ℝ => (physicalSliceLambda A s₀ κ Λ h (T - t))⁻¹ /
      ((Λ ^ A * A ^ (-((A + 1) / 2))) * (T - t) ^ ((A + 1) / 2)) - 1)
      =O[𝓝[<] T] (fun t : ℝ => (T - t) ^ (A * δ)) := by
  simpa only [Function.comp_def] using
    (physicalSliceLambda_rate_error_isBigO h hA hs₀ hδ hδ1 hH hΛ hh hbound hsmall hκ).comp_tendsto
      (remainingTime_tendsto_zero_right T)

/-- The quantitative logarithmic phase law in the original physical time. -/
theorem physicalSliceGamma_log_error_at_terminal
    {A s₀ κ δ H J Λ θ γ : ℝ} (h g : ℝ → ℝ) (T : ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hg : ContinuousOn g (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (gbound : ∀ s : ℝ, s₀ ≤ s → |g s| ≤ J * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun t : ℝ => physicalSliceGamma A s₀ κ Λ θ γ h g (T - t) -
      θ * Real.log (T - t) - (γ - θ * Real.log (A / Λ ^ 2)))
      =O[𝓝[<] T] (fun t : ℝ => (T - t) ^ (A * δ)) := by
  simpa only [Function.comp_def] using
    (physicalSliceGamma_log_error_isBigO (θ := θ) (γ := γ) h g hA hs₀ hδ hδ1
      hH hΛ hh hg hbound gbound hsmall hκ).comp_tendsto (remainingTime_tendsto_zero_right T)

end HBL.Kinematic
