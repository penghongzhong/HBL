import HBL.KinematicPhysicalPhase

/-! The actual phase tail solves its prescribed differential equation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Kinematic

/-- The derivative of a continuous absolutely integrable tail on the open half-line. -/
theorem phaseTailIntegral_hasDerivAt
    {f : ℝ → ℝ} {s₀ s : ℝ} (hc : ContinuousOn f (Ici s₀))
    (hint : IntegrableOn f (Ioi s₀)) (hs : s₀ < s) :
    HasDerivAt (fun x => ∫ t in Ioi x, f t) (-f s) s := by
  have hi : IntervalIntegrable f volume s₀ s :=
    (hc.mono (fun _ hx => hx.1)).intervalIntegrable_of_Icc hs.le
  have hm : StronglyMeasurableAtFilter f (𝓝 s) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hc.mono Ioi_subset_Ici_self) s hs
  have hd := intervalIntegral.integral_hasDerivAt_right hi hm
    ((hc s hs.le).continuousAt (Ici_mem_nhds hs))
  have hmodel : HasDerivAt
      (fun x => (∫ t in Ioi s₀, f t) - ∫ t in s₀..x, f t) (-f s) s := by
    convert (hasDerivAt_const s (∫ t in Ioi s₀, f t)).sub hd using 1
    ring
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with x hx
  have heq := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hx.le))
  linarith

/-- The original phase integrand is integrable as a consequence of the actual path bounds. -/
theorem sliceGamma_integrand_integrable_of_path
    {A s₀ κ δ H J θ : ℝ} (h g : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hg : ContinuousOn g (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (gbound : ∀ s : ℝ, s₀ ≤ s → |g s| ≤ J * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    IntegrableOn (fun t => (θ + g t) / sliceClock A s₀ κ h t - θ / (A * t))
      (Ioi s₀) := by
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have hqc := (sliceClock_continuousOn A s₀ κ h hh).mono Ioi_subset_Ici_self
  have hql : ∀ s ∈ Ioi s₀, (A / 2) * s ≤ sliceClock A s₀ κ h s := by
    intro s hs
    exact (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs.le).1
  have hgint := phaseQuotient_integrableOn hs₀ hδ (show 0 < A / 2 by positivity)
    hqc (hg.mono Ioi_subset_Ici_self) hql (fun s hs => gbound s hs.le)
  have hi : (fun t => (θ + g t) / sliceClock A s₀ κ h t - θ / (A * t)) =
      (fun t => θ * sliceIntegrand A s₀ κ h t + g t / sliceClock A s₀ κ h t) := by
    funext t
    unfold sliceIntegrand
    simp only [div_eq_mul_inv]
    ring
  rw [hi]
  exact (hint.const_mul θ).add hgint

/-- The phase defined by the original tail integral satisfies `γₛ = -(θ + g) / q`.
No phase integrability or differentiability is assumed. -/
theorem sliceGamma_hasDerivAt_of_path
    {A s₀ κ δ H J θ γ s : ℝ} (h g : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hg : ContinuousOn g (Ici s₀))
    (hbound : ∀ t : ℝ, s₀ ≤ t → |h t| ≤ H * t ^ (-δ))
    (gbound : ∀ t : ℝ, s₀ ≤ t → |g t| ≤ J * t ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) (hs : s₀ < s) :
    HasDerivAt (sliceGamma A s₀ κ θ γ h g)
      (-(θ + g s) / sliceClock A s₀ κ h s) s := by
  have hq : ∀ t ∈ Ici s₀, 0 < sliceClock A s₀ κ h t := by
    intro t ht
    exact (mul_pos (show 0 < A / 2 by positivity) (hs₀.trans_le ht)).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ ht).1
  have hqc := sliceClock_continuousOn A s₀ κ h hh
  have hc : ContinuousOn
      (fun t => (θ + g t) / sliceClock A s₀ κ h t - θ / (A * t)) (Ici s₀) :=
    ((continuousOn_const.add hg).div hqc (fun t ht => (hq t ht).ne')).sub
      (continuousOn_const.div (continuous_const.mul continuous_id).continuousOn
        (fun t ht => (mul_pos hA (hs₀.trans_le ht)).ne'))
  have hint := sliceGamma_integrand_integrable_of_path (θ := θ) h g hA hs₀ hδ hδ1
    hH hh hg hbound gbound hsmall hκ
  have hd := phaseTailIntegral_hasDerivAt hc hint hs
  have hlog := (Real.hasDerivAt_log (hs₀.trans hs).ne').const_mul (θ / A)
  convert ((hasDerivAt_const s γ).sub hlog).add hd using 1
  · rfl
  · field_simp [hA.ne', (hs₀.trans hs).ne', (hq s hs.le).ne']
    ring

end HBL.Kinematic
