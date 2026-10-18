import HBL.KinematicPhaseTail

/-! The actual phase integral and its physical-time logarithmic expansion. -/

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace HBL.Kinematic

/-- The phase prescribed by the common terminal phase in the kinematic reconstruction. -/
def sliceGamma (A s₀ κ θ γ : ℝ) (h g : ℝ → ℝ) (s : ℝ) : ℝ :=
  γ - (θ / A) * Real.log s +
    ∫ t in Ioi s, (θ + g t) / sliceClock A s₀ κ h t - θ / (A * t)

/-- The reciprocal-clock tail cancels exactly when phase is expressed in physical time. -/
theorem sliceGamma_sub_log_physicalTime_eq
    {A s₀ κ Λ θ γ s : ℝ} {h g : ℝ → ℝ}
    (hA : 0 < A) (hs : 0 < s) (hΛ : 0 < Λ)
    (hq : 0 < sliceClock A s₀ κ h s)
    (hint : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s))
    (hgint : IntegrableOn (fun t => g t / sliceClock A s₀ κ h t) (Ioi s)) :
    sliceGamma A s₀ κ θ γ h g s - θ * Real.log (slicePhysicalTime A s₀ κ Λ h s) -
      (γ - θ * Real.log (A / Λ ^ 2)) =
      ∫ t in Ioi s, g t / sliceClock A s₀ κ h t := by
  have hi : (fun t => (θ + g t) / sliceClock A s₀ κ h t - θ / (A * t)) =
      (fun t => θ * sliceIntegrand A s₀ κ h t + g t / sliceClock A s₀ κ h t) := by
    funext t
    unfold sliceIntegrand
    simp only [div_eq_mul_inv]
    ring
  have hB : 0 < A / Λ ^ 2 := div_pos hA (sq_pos_of_pos hΛ)
  unfold sliceGamma
  rw [hi, integral_add (hint.const_mul θ) hgint, integral_const_mul]
  rw [slicePhysicalTime_eq_reference_mul_exp hA hs hΛ hq,
    sliceReferenceTime_eq_power hA hs,
    Real.log_mul (mul_pos hB (Real.rpow_pos_of_pos hs _)).ne' (Real.exp_pos _).ne',
    Real.log_mul hB.ne' (Real.rpow_pos_of_pos hs _).ne',
    Real.log_rpow hs, Real.log_exp]
  unfold sliceTailFrom
  simp only [div_eq_mul_inv]
  ring

/-- The actual two-component path yields a power error after its physical logarithmic phase.
The only inputs are continuity, decay and the clock's existing smallness conditions. -/
theorem sliceGamma_physical_error_isBigO
    {A s₀ κ δ H J Λ θ γ : ℝ} (h g : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hg : ContinuousOn g (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (gbound : ∀ s : ℝ, s₀ ≤ s → |g s| ≤ J * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    (fun s : ℝ => sliceGamma A s₀ κ θ γ h g s -
      θ * Real.log (slicePhysicalTime A s₀ κ Λ h s) -
      (γ - θ * Real.log (A / Λ ^ 2))) =O[atTop]
      (fun s : ℝ => slicePhysicalTime A s₀ κ Λ h s ^ (A * δ)) := by
  have hc : 0 < A / 2 := by positivity
  have hqc := (sliceClock_continuousOn A s₀ κ h hh).mono Ioi_subset_Ici_self
  have hgc := hg.mono Ioi_subset_Ici_self
  have hql : ∀ s ∈ Ioi s₀, (A / 2) * s ≤ sliceClock A s₀ κ h s := by
    intro s hs
    exact (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs.le).1
  have hgb : ∀ s ∈ Ioi s₀, |g s| ≤ J * s ^ (-δ) := fun s hs => gbound s hs.le
  have hG := phaseQuotient_tail_isBigO hs₀ hδ hc hqc hgc hql hgb
  have hgint := phaseQuotient_integrableOn hs₀ hδ hc hqc hgc hql hgb
  have hint := sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ
  have htime := rpow_neg_isBigO_slicePhysicalTime_rpow h hA hs₀ hδ hδ1 hH hΛ
    hh hbound hsmall hκ
  apply (hG.trans htime).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop s₀] with s hs
  have hqpos : 0 < sliceClock A s₀ κ h s :=
    (mul_pos hc (hs₀.trans hs)).trans_le (hql s hs)
  exact (sliceGamma_sub_log_physicalTime_eq hA (hs₀.trans hs) hΛ hqpos
    (hint.mono_set (Ioi_subset_Ioi hs.le))
    (hgint.mono_set (Ioi_subset_Ioi hs.le))).symm

end HBL.Kinematic
