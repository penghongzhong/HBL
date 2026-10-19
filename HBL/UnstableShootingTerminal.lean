import HBL.UnstableShootingBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The actual terminal integral solves the nonautonomous scalar equation and is
the unique bounded solution on the closed initial half-line.  Differentiation
uses a fixed-base integrating factor and the ordinary fundamental theorem of
calculus.  Uniqueness uses the actual kernel, its exponential decay, and the
fundamental theorem on a half-line, including its initial endpoint.

These results concern primitive continuous scalar coefficients and sources.
Their identification with the Hartree unstable spectral coordinate, and the
corresponding physical-time path bounds, remain separate obligations.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Shooting

private theorem terminalTail_eq_total_sub_interval
    {w : ℝ → ℝ} {s₀ s : ℝ} (hint : IntegrableOn w (Ioi s₀)) (hs : s₀ ≤ s) :
    (∫ t in Ioi s, w t) = (∫ t in Ioi s₀, w t) - ∫ t in s₀..s, w t := by
  have hi := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hs))
  linarith

private theorem terminalTail_hasDerivAt
    {w : ℝ → ℝ} {s₀ s : ℝ} (hw : Continuous w)
    (hint : IntegrableOn w (Ioi s₀)) (hs : s₀ < s) :
    HasDerivAt (fun x => ∫ t in Ioi x, w t) (-w s) s := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hw.intervalIntegrable s₀ s)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hm : HasDerivAt
      (fun x => (∫ t in Ioi s₀, w t) - ∫ t in s₀..x, w t) (-w s) s := by
    convert (hasDerivAt_const s (∫ t in Ioi s₀, w t)).sub hd using 1
    ring
  apply hm.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact terminalTail_eq_total_sub_interval hint hx.le

private theorem terminalSolution_eq_fixedBase
    {a f : ℝ → ℝ} (ha : Continuous a) (s₀ s : ℝ) :
    unstableShootingSolution a f s =
      -(Real.exp (∫ t in s₀..s, a t)) *
        (∫ t in Ioi s, unstableShootingKernel a s₀ t * f t) := by
  unfold unstableShootingSolution
  simp_rw [unstableShootingKernel_factorization ha s₀ s, mul_assoc]
  rw [integral_const_mul]
  ring

/-- The explicitly constructed terminal integral satisfies the actual ODE.
Absolute convergence is derived from the primitive rate and source bounds. -/
theorem unstableShootingSolution_hasDerivAt
    {a f : ℝ → ℝ} {s₀ p e F s : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p))
    (hs : s₀ < s) :
    HasDerivAt (unstableShootingSolution a f)
      (a s * unstableShootingSolution a f s + f s) s := by
  have hw := (unstableShootingKernel_continuous_right ha s₀).mul hf
  have hi := unstableShootingSolution_integrable hs₀ hp he hF ha hf hrate hsource
    (le_refl s₀)
  have hd := terminalTail_hasDerivAt hw hi hs
  have hA := intervalIntegral.integral_hasDerivAt_right
    (ha.intervalIntegrable s₀ s)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hc : Real.exp (∫ t in s₀..s, a t) * unstableShootingKernel a s₀ s = 1 := by
    rw [unstableShootingKernel, ← Real.exp_add]
    simp
  have hm := hA.exp.neg.mul hd
  have heq : (fun x => -(Real.exp (∫ t in s₀..x, a t)) *
      (∫ t in Ioi x, unstableShootingKernel a s₀ t * f t)) =
      unstableShootingSolution a f := by
    funext x
    exact (terminalSolution_eq_fixedBase ha s₀ x).symm
  change HasDerivAt (fun x => -(Real.exp (∫ t in s₀..x, a t)) *
    (∫ t in Ioi x, unstableShootingKernel a s₀ t * f t)) _ s at hm
  simp only [Pi.mul_apply, Pi.neg_apply] at hm
  rw [heq] at hm
  convert hm using 1
  rw [terminalSolution_eq_fixedBase ha s₀ s]
  nlinarith [congrArg (fun x : ℝ => x * f s) hc]

/-- The terminal solution is continuous up to the initial endpoint. -/
theorem unstableShootingSolution_continuousOn
    {a f : ℝ → ℝ} {s₀ p e F : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p)) :
    ContinuousOn (unstableShootingSolution a f) (Ici s₀) := by
  have hw := (unstableShootingKernel_continuous_right ha s₀).mul hf
  have hi := unstableShootingSolution_integrable hs₀ hp he hF ha hf hrate hsource
    (le_refl s₀)
  have hA : Continuous (fun x => ∫ t in s₀..x, a t) :=
    (intervalIntegral.differentiable_integral_of_continuous ha).continuous
  have hW : Continuous (fun x => ∫ t in s₀..x,
      unstableShootingKernel a s₀ t * f t) :=
    (intervalIntegral.differentiable_integral_of_continuous hw).continuous
  have hT : Continuous (fun _ : ℝ =>
      ∫ t in Ioi s₀, unstableShootingKernel a s₀ t * f t) := continuous_const
  apply ((Real.continuous_exp.comp hA).neg.mul
    (hT.sub hW)).continuousOn.congr
  intro s hs
  rw [terminalSolution_eq_fixedBase ha s₀ s,
    terminalTail_eq_total_sub_interval hi hs]
  rfl

private theorem terminalWeightedBounded_tendsto_zero
    {a y : ℝ → ℝ} {s₀ e C s : ℝ}
    (he : 0 < e) (hC : 0 ≤ C) (ha : Continuous a)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hybound : ∀ t, s₀ ≤ t → |y t| ≤ C) (hs : s₀ ≤ s) :
    Tendsto (fun t => unstableShootingKernel a s t * y t) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => e * (t - s)) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (B / e + s)] with t ht
    have hb : B / e ≤ t - s := by linarith
    simpa only [mul_comm] using (div_le_iff₀ he).mp hb
  have hexp : Tendsto (fun t : ℝ => C * Real.exp (-e * (t - s))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).const_mul C
  apply squeeze_zero_norm' _ hexp
  filter_upwards [eventually_ge_atTop s] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (unstableShootingKernel_pos a s t)]
  have hk := unstableShootingKernel_le_exp ht ha.continuousOn
    (fun x hx => hrate x (hs.trans hx.1))
  calc
    unstableShootingKernel a s t * |y t| ≤ unstableShootingKernel a s t * C :=
      mul_le_mul_of_nonneg_left (hybound t (hs.trans ht))
        (unstableShootingKernel_pos a s t).le
    _ ≤ Real.exp (-e * (t - s)) * C := mul_le_mul_of_nonneg_right hk hC
    _ = _ := by ring

/-- Any bounded solution of the same scalar ODE, continuous at its initial
endpoint, equals the actual terminal integral on the whole closed half-line. -/
theorem unstableShootingSolution_unique_bounded
    {a f y : ℝ → ℝ} {s₀ p e F : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p))
    (hycont : ContinuousOn y (Ici s₀))
    (hyderiv : ∀ t, s₀ < t → HasDerivAt y (a t * y t + f t) t)
    (hybound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, s₀ ≤ t → |y t| ≤ C) :
    ∀ s, s₀ ≤ s → y s = unstableShootingSolution a f s := by
  rcases hybound with ⟨C, hC, hybound⟩
  intro s hs
  have hcont : ContinuousWithinAt
      (fun t => unstableShootingKernel a s t * y t) (Ici s) s :=
    (unstableShootingKernel_continuous_right ha s).continuousWithinAt.mul
      ((hycont s hs).mono (Ici_subset_Ici.mpr hs))
  have hd : ∀ t ∈ Ioi s, HasDerivAt
      (fun x => unstableShootingKernel a s x * y x)
      (unstableShootingKernel a s t * f t) t := by
    intro t ht
    convert (unstableShootingKernel_hasDerivAt_right ha s t).mul
      (hyderiv t (hs.trans_lt ht)) using 1
    ring
  have hi := unstableShootingSolution_integrable hs₀ hp he hF ha hf hrate hsource hs
  have ht := terminalWeightedBounded_tendsto_zero he hC ha hrate hybound hs
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hi ht
  simp only [unstableShootingKernel_self, one_mul, zero_sub] at hFTC
  unfold unstableShootingSolution
  linarith

/-- The constructed solution belongs to the bounded solution class in which
the preceding uniqueness statement applies. -/
theorem unstableShootingSolution_bounded
    {a f : ℝ → ℝ} {s₀ p e F : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s, s₀ ≤ s → |unstableShootingSolution a f s| ≤ C := by
  refine ⟨(F / e) * s₀ ^ (-p), mul_nonneg (div_nonneg hF he.le)
    (Real.rpow_nonneg hs₀.le _), ?_⟩
  intro s hs
  exact (unstableShootingSolution_bound hs₀ hp he hF ha hf hrate hsource hs).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hs₀ hs (neg_nonpos.mpr hp.le))
      (div_nonneg hF he.le))

/-- Complete revised scalar shooting environment.  Every analytic output
concerns the actual coefficient-integral kernel and terminal source integral;
the inputs are only bounds and continuity of the primitive paths.  The
candidate ODE hypotheses occur exclusively inside the uniqueness conclusion. -/
theorem revisedUnstableShootingManuscriptEnvironment_closed
    {a f : ℝ → ℝ} {s₀ p e F : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p)) :
    (∀ s, s₀ ≤ s → IntegrableOn
      (fun t => unstableShootingKernel a s t * f t) (Ioi s)) ∧
    ContinuousOn (unstableShootingSolution a f) (Ici s₀) ∧
    (∀ s, s₀ < s → HasDerivAt (unstableShootingSolution a f)
      (a s * unstableShootingSolution a f s + f s) s) ∧
    (∀ s, s₀ ≤ s → |unstableShootingSolution a f s| ≤ (F / e) * s ^ (-p)) ∧
    Tendsto (unstableShootingSolution a f) atTop (𝓝 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s, s₀ ≤ s → |unstableShootingSolution a f s| ≤ C) ∧
    (∀ y : ℝ → ℝ, ContinuousOn y (Ici s₀) →
      (∀ t, s₀ < t → HasDerivAt y (a t * y t + f t) t) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, s₀ ≤ t → |y t| ≤ C) →
      ∀ s, s₀ ≤ s → y s = unstableShootingSolution a f s) ∧
    (∀ (b g : ℝ → ℝ) (D E G ρ : ℝ),
      0 ≤ D → 0 ≤ E → 0 ≤ G → 0 ≤ ρ →
      Continuous b → Continuous g →
      (∀ t, s₀ ≤ t → e ≤ b t) →
      (∀ t, s₀ ≤ t → |a t - b t| ≤ D * t ^ (-ρ)) →
      (∀ t, s₀ ≤ t → |g t| ≤ G * t ^ (-p)) →
      (∀ t, s₀ ≤ t → |f t - g t| ≤ E * t ^ (-p)) →
      ∀ s, s₀ ≤ s →
        |unstableShootingSolution a f s - unstableShootingSolution b g s| ≤
          (E / e) * s ^ (-p) + (G * D / e ^ 2) * s ^ (-p - ρ)) := by
  refine ⟨(fun s hs => unstableShootingSolution_integrable hs₀ hp he hF
      ha hf hrate hsource hs),
    unstableShootingSolution_continuousOn hs₀ hp he hF ha hf hrate hsource,
    (fun s hs => unstableShootingSolution_hasDerivAt hs₀ hp he hF
      ha hf hrate hsource hs),
    (fun s hs => unstableShootingSolution_bound hs₀ hp he hF ha hf hrate hsource hs),
    unstableShootingSolution_tendsto_zero hs₀ hp he hF ha hf hrate hsource,
    unstableShootingSolution_bounded hs₀ hp he hF ha hf hrate hsource,
    (fun y hycont hyderiv hybound => unstableShootingSolution_unique_bounded
      hs₀ hp he hF ha hf hrate hsource hycont hyderiv hybound), ?_⟩
  intro b g D E G ρ hD hE hG hρ hb hg hrateb hratediff hsourceg hsourcediff s hs
  exact unstableShootingSolution_difference_bound_of_rate_decay hs₀ hp hρ he
    hD hE hF hG ha hb hf hg hrate hrateb hratediff hsource hsourceg hsourcediff hs

end HBL.Shooting
