import HBL.KinematicSynchronizedSliceCertified

/-!
# The complete original synchronized-slice environment

This is the single terminal for manuscript `prop:kinematic-recovery-v2`.
Its assumptions are the original continuous-path bound and quantitative
smallness condition. The clock and scale are the actual integral formulas;
the terminal amplitude is fixed and shared by both paths.

The conclusion retains every clause of the original environment: the clock
bounds and absolute tail convergence for every admissible shift and every
later time, the explicitly selected unique synchronized root, its size, and
the exact two-path comparison. All these statements are assembled from the
existing scalar-clock proofs. No PDE orbit or new environment is asserted.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.Kinematic

/-- Full quantifier-preserving terminal for `prop:kinematic-recovery-v2`.
The selected parameter itself supplies existence; the fourth conjunct gives
uniqueness among all admissible roots of the physical slice equation. -/
theorem kinematicRecovery_originalEnvironment_closed
    {A s₀ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32) :
    (∀ κ : ℝ, |κ| ≤ A * s₀ / 4 → ∀ s : ℝ, s₀ ≤ s →
      A * s / 2 ≤ sliceClock A s₀ κ h s ∧
      sliceClock A s₀ κ h s ≤ 2 * A * s ∧
      IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s)) ∧
    |synchronizedSliceParameter A s₀ h| ≤ A * s₀ / 4 ∧
    sliceClock A s₀ (synchronizedSliceParameter A s₀ h) h s₀ /
        sliceLambda A s₀ (synchronizedSliceParameter A s₀ h) Λ h s₀ ^ 2 =
      A * s₀ / (Λ * s₀ ^ sliceBeta A) ^ 2 ∧
    (∀ η : ℝ, |η| ≤ A * s₀ / 4 →
      sliceClock A s₀ η h s₀ / sliceLambda A s₀ η Λ h s₀ ^ 2 =
        A * s₀ / (Λ * s₀ ^ sliceBeta A) ^ 2 →
      η = synchronizedSliceParameter A s₀ h) ∧
    |synchronizedSliceParameter A s₀ h| ≤
      (32 * H / (δ * (1 - δ))) * s₀ ^ (1 - δ) ∧
    (∀ (k : ℝ → ℝ) (J D : ℝ),
      0 ≤ J → 0 ≤ D → ContinuousOn k (Ici s₀) →
      (∀ s : ℝ, s₀ ≤ s → |k s| ≤ J * s ^ (-δ)) →
      (∀ s : ℝ, s₀ ≤ s → |h s - k s| ≤ D * s ^ (-δ)) →
      (4 * J / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32 →
      |synchronizedSliceParameter A s₀ h - synchronizedSliceParameter A s₀ k| ≤
        (64 * D / (δ * (1 - δ))) * s₀ ^ (1 - δ)) := by
  have hsmall' : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4 :=
    hsmall.trans (by nlinarith [mul_lt_mul_of_pos_left hδ1 hA])
  have hsync := synchronized_initial_slice_certified h hA hs₀ hδ hδ1 hH hΛ
    hh hbound hsmall
  refine ⟨?_, hsync.1, hsync.2.1, hsync.2.2.2, hsync.2.2.1, ?_⟩
  · intro κ hκ s hs
    have hclock := sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound
      hsmall' hκ hs
    refine ⟨by nlinarith [hclock.1], hclock.2, ?_⟩
    exact (sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound
      hsmall' hκ).mono_set (fun t ht => hs.trans_lt ht)
  · intro k J D hJ hD hk kbound hgap ksmall
    exact synchronizedSliceParameter_stability h k hA hs₀ hδ hδ1 hH hJ hD
      hh hk hbound kbound hgap hsmall ksmall

end HBL.Kinematic
