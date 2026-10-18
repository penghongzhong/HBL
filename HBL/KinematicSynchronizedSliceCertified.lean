import HBL.KinematicPathTailDifference
import HBL.KinematicSliceDynamics

/-!
The synchronized initial slice in physical time.  The scalar root is built
from the actual path integral; this terminal statement has only the path's
continuity, decay and quantitative smallness as analytic hypotheses.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

/-- The normalization really solves the kinematic equations and has the
prescribed terminal amplitude for the actual decaying path.  Clock positivity
and every tail's integrability are proved here from the same path hypotheses. -/
theorem slice_kinematics_of_path
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (∀ s : ℝ, s₀ ≤ s →
      (A / 2 * s ≤ sliceClock A s₀ κ h s ∧ sliceClock A s₀ κ h s ≤ 2 * A * s) ∧
        IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s)) ∧
    (∀ s : ℝ, s₀ < s →
      HasDerivAt (fun t => Real.log (sliceLambda A s₀ κ Λ h t))
        ((A + 4 * h s + 1) / (2 * sliceClock A s₀ κ h s)) s ∧
      HasDerivAt (sliceLambda A s₀ κ Λ h)
        (((A + 4 * h s + 1) / (2 * sliceClock A s₀ κ h s)) *
          sliceLambda A s₀ κ Λ h s) s ∧
      HasDerivAt (slicePhysicalTime A s₀ κ Λ h)
        (-(sliceLambda A s₀ κ Λ h s ^ 2)⁻¹) s) ∧
    Tendsto (fun s : ℝ => sliceLambda A s₀ κ Λ h s / (Λ * s ^ sliceBeta A))
      atTop (𝓝 1) := by
  have hb := fun s hs => sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound
    hsmall hκ (s := s) hs
  have hq : ∀ t : ℝ, s₀ ≤ t → 0 < sliceClock A s₀ κ h t := by
    intro t ht
    exact (mul_pos (by positivity : 0 < A / 2) (hs₀.trans_le ht)).trans_le (hb t ht).1
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact ⟨hb s hs, hint.mono_set (fun t ht => hs.trans_lt ht)⟩
  · intro s hs
    exact ⟨sliceLambda_log_hasDerivAt h hA hs₀ hΛ hh hq hint hs,
      sliceLambda_hasDerivAt h hA hs₀ hΛ hh hq hint hs,
      slicePhysicalTime_hasDerivAt h hA hs₀ hΛ hh hq hint hs⟩
  · exact sliceLambda_div_terminal_tendsto_one_of_path_bound h hA hs₀ hΛ
      hδ hδ1 hH hbound hint

/-- Existence, quantitative size and uniqueness on the admissible parameter
interval for the common initial physical-time slice.  The terminal amplitude
`Λ` is shared by all paths and is not adjusted to solve the slice equation. -/
theorem synchronized_initial_slice_certified
    {A s₀ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32) :
    |synchronizedSliceParameter A s₀ h| ≤ A * s₀ / 4 ∧
      slicePhysicalTime A s₀ (synchronizedSliceParameter A s₀ h) Λ h s₀ =
        sliceReferenceTime A Λ s₀ ∧
      |synchronizedSliceParameter A s₀ h| ≤
        (32 * H / (δ * (1 - δ))) * s₀ ^ (1 - δ) ∧
      ∀ η : ℝ, |η| ≤ A * s₀ / 4 →
        slicePhysicalTime A s₀ η Λ h s₀ = sliceReferenceTime A Λ s₀ →
        η = synchronizedSliceParameter A s₀ h := by
  have hp := synchronizedSliceParameter_spec h hA hs₀ hδ hδ1 hH hh hbound hsmall
  have hq : ∀ η : ℝ, |η| ≤ A * s₀ / 4 →
      0 < sliceClock A s₀ η h s₀ := by
    intro η hη
    rw [sliceClock_initial]
    have hηlower := (abs_le.mp hη).1
    have hAs : 0 < A * s₀ := mul_pos hA hs₀
    linarith
  refine ⟨hp.1, ?_, hp.2.2.1, ?_⟩
  · exact (synchronized_slice_iff_tail_zero hA hs₀ hΛ (hq _ hp.1)).2 hp.2.1
  · intro η hη htime
    exact hp.2.2.2 η hη
      ((synchronized_slice_iff_tail_zero hA hs₀ hΛ (hq η hη)).1 htime)

end HBL.Kinematic
