import HBL.MonopoleMovingCutoffSpatial
import HBL.MonopoleRadialOrigin
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
Full positive-half-line reduced radial gradient energy of the actual moving
cutoff monopole.  The transition annulus is included.  All bounds come from
the already constructed profile and the fixed smooth cutoff, and remain
valid through zero amplitude.  No finite-profile, radiation, Kummer matching,
three-dimensional weak equation or homogeneous-Sobolev lift is asserted.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The actual cutoff profile increment, without changing its positive-radius
representative. -/
def monopoleMovingCutoffIncrement (c r : ℝ) : ℝ :=
  monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r - bubble r

theorem monopoleMovingCutoffIncrement_eq (c r : ℝ) :
    monopoleMovingCutoffIncrement c r =
      c * (1 - cutoff (|c| * r / 4)) * monopoleRadialProfile r := by
  rw [monopoleMovingCutoffIncrement, monopoleMovingCutoffProfile_eq]
  ring

@[simp] theorem monopoleMovingCutoffIncrement_zero :
    monopoleMovingCutoffIncrement 0 = fun _ => 0 := by
  funext r
  simp [monopoleMovingCutoffIncrement_eq]

/-- Genuine spatial derivative of the increment, including its annular term. -/
theorem monopoleMovingCutoffIncrement_hasDerivAt (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (monopoleMovingCutoffIncrement c)
      (c * ((1 - cutoff (|c| * r / 4)) * deriv monopoleRadialProfile r -
        (|c| / 4) * deriv cutoff (|c| * r / 4) * monopoleRadialProfile r)) r := by
  convert (monopoleMovingCutoffSpatial_hasDerivAt c hr).sub
    (bubble_differentiable r).hasDerivAt using 1
  · rfl
  · ring

private theorem energyCutoff_derivative_has_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ Icc (0 : ℝ) 2, |deriv cutoff z| ≤ K := by
  have hc : Continuous (deriv cutoff) :=
    (contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).2.continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 2) hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro z hz
  have hb := hB z hz
  rw [Real.norm_eq_abs] at hb
  exact hb.trans (by linarith [le_abs_self B])

private def energyCutoffDerivativeConstant : ℝ :=
  Classical.choose energyCutoff_derivative_has_bound

private theorem energyCutoffDerivativeConstant_spec :
    0 < energyCutoffDerivativeConstant ∧
      ∀ z ∈ Icc (0 : ℝ) 2, |deriv cutoff z| ≤ energyCutoffDerivativeConstant :=
  Classical.choose_spec energyCutoff_derivative_has_bound

private def energyDilationConstant : ℝ :=
  Classical.choose monopoleRadialProfile_dilation_bounded

private theorem energyDilationConstant_spec :
    0 < energyDilationConstant ∧ ∀ r, 0 < r →
      |dilationGenerator monopoleRadialProfile r| ≤ energyDilationConstant :=
  Classical.choose_spec monopoleRadialProfile_dilation_bounded

private def energyWeightedDerivativeConstant : ℝ :=
  energyDilationConstant + monopoleRadialBoundConstant / 2 +
    2 * energyCutoffDerivativeConstant * monopoleRadialBoundConstant

/-- An amplitude-independent constant derived from proved global profile and
dilation bounds and the derivative bound of the fixed cutoff on [0,2]. -/
def monopoleGlobalEnergyConstant : ℝ := 8 * energyWeightedDerivativeConstant ^ 2

theorem monopoleGlobalEnergyConstant_pos : 0 < monopoleGlobalEnergyConstant := by
  have hD := energyDilationConstant_spec.1
  have hK := energyCutoffDerivativeConstant_spec.1
  have hB := monopoleRadialBoundConstant_pos
  unfold monopoleGlobalEnergyConstant energyWeightedDerivativeConstant
  positivity

private theorem monopole_weighted_derivative_bound {r : ℝ} (hr : 0 < r) :
    |r * deriv monopoleRadialProfile r| ≤
      energyDilationConstant + monopoleRadialBoundConstant / 2 := by
  have hid : r * deriv monopoleRadialProfile r =
      dilationGenerator monopoleRadialProfile r - monopoleRadialProfile r / 2 := by
    unfold dilationGenerator
    ring
  rw [hid]
  have htri (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  refine (htri _ _).trans (add_le_add (energyDilationConstant_spec.2 r hr) ?_)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (monopoleRadialProfile_abs_le hr) (by norm_num)

private theorem movingCutoff_weighted_derivative_bound
    {c r : ℝ} (hr : 0 < r) (hz : |c| * r / 4 ≤ 2) :
    |r * deriv (monopoleMovingCutoffIncrement c) r| ≤
      |c| * energyWeightedDerivativeConstant := by
  let z : ℝ := |c| * r / 4
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz2 : z ≤ 2 := hz
  have hcut0 : 0 ≤ cutoff z := Real.smoothTransition.nonneg (z - 1)
  have hcut1 : cutoff z ≤ 1 := Real.smoothTransition.le_one (z - 1)
  have hcut : |1 - cutoff z| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hcut1)]
    linarith
  have hfirst : |(1 - cutoff z) * (r * deriv monopoleRadialProfile r)| ≤
      energyDilationConstant + monopoleRadialBoundConstant / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hcut (abs_nonneg _)).trans
      (by simpa only [one_mul] using monopole_weighted_derivative_bound hr)
  have hsecond : |z * deriv cutoff z * monopoleRadialProfile r| ≤
      2 * energyCutoffDerivativeConstant * monopoleRadialBoundConstant := by
    rw [abs_mul, abs_mul, abs_of_nonneg hz0]
    have hK := energyCutoffDerivativeConstant_spec
    have hKpos := hK.1
    have hB := monopoleRadialBoundConstant_pos
    exact mul_le_mul (mul_le_mul hz2 (hK.2 z ⟨hz0, hz2⟩)
      (abs_nonneg _) (by norm_num)) (monopoleRadialProfile_abs_le hr)
      (abs_nonneg _) (by positivity)
  have hid : r * deriv (monopoleMovingCutoffIncrement c) r =
      c * ((1 - cutoff z) * (r * deriv monopoleRadialProfile r) -
        z * deriv cutoff z * monopoleRadialProfile r) := by
    rw [(monopoleMovingCutoffIncrement_hasDerivAt c hr).deriv]
    dsimp [z]
    ring
  rw [hid, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  have htri (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  exact (htri _ _).trans (add_le_add hfirst hsecond)

private theorem movingCutoff_derivative_zero_outside
    {c r : ℝ} (hc : c ≠ 0) (hr : 8 / |c| < r) :
    deriv (monopoleMovingCutoffIncrement c) r = 0 := by
  have habs : 0 < |c| := abs_pos.mpr hc
  have he : monopoleMovingCutoffIncrement c =ᶠ[𝓝 r] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    have harg : 2 ≤ |c| * x / 4 := by
      have h := (div_lt_iff₀ habs).mp hx
      nlinarith
    rw [monopoleMovingCutoffIncrement_eq, cutoff_one_of_two_le _ harg]
    ring
  rw [he.deriv_eq]
  exact deriv_const r 0

/-- Actual nonnegative reduced radial gradient-energy density. -/
def monopoleMovingCutoffGradientEnergyDensity (c r : ℝ) : ℝ :=
  r ^ 2 * |deriv (monopoleMovingCutoffIncrement c) r| ^ 2

private theorem movingCutoff_energyDensity_measurable (c : ℝ) :
    Measurable (monopoleMovingCutoffGradientEnergyDensity c) := by
  unfold monopoleMovingCutoffGradientEnergyDensity
  fun_prop

private theorem movingCutoff_energyDensity_nonneg (c r : ℝ) :
    0 ≤ monopoleMovingCutoffGradientEnergyDensity c r := by
  unfold monopoleMovingCutoffGradientEnergyDensity
  positivity

private theorem movingCutoff_energyDensity_bound
    {c r : ℝ} (hc : c ≠ 0) (hr : 0 < r) :
    monopoleMovingCutoffGradientEnergyDensity c r ≤
      energyWeightedDerivativeConstant ^ 2 * c ^ 2 := by
  by_cases hout : 8 / |c| < r
  · simpa only [monopoleMovingCutoffGradientEnergyDensity,
      movingCutoff_derivative_zero_outside hc hout, abs_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero] using mul_nonneg (sq_nonneg energyWeightedDerivativeConstant) (sq_nonneg c)
  · have hz : |c| * r / 4 ≤ 2 := by
      have h := (le_div_iff₀ (abs_pos.mpr hc)).mp (le_of_not_gt hout)
      nlinarith
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (movingCutoff_weighted_derivative_bound hr hz) 2
    simpa only [monopoleMovingCutoffGradientEnergyDensity, abs_mul, mul_pow, sq_abs,
      mul_comm (c ^ 2)] using h

/-- Replace only the origin value by the actual source-mass limit. -/
def monopoleMovingCutoffContinuous (c r : ℝ) : ℝ :=
  bubble r + c * monopoleInnerRadialContinuous (monopoleQuadraticRadius c) r

theorem monopoleMovingCutoffContinuous_eq (c : ℝ) {r : ℝ} (hr : 0 < r) :
    monopoleMovingCutoffContinuous c r =
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r := by
  rw [monopoleMovingCutoffContinuous, monopoleInnerRadialContinuous_eq hr]
  rfl

theorem monopoleMovingCutoffContinuous_origin (c : ℝ) :
    monopoleMovingCutoffContinuous c 0 = 1 + c * monopoleRadialOriginValue := by
  simp [monopoleMovingCutoffContinuous, bubble]

theorem monopoleMovingCutoffContinuous_continuousOn (c : ℝ) :
    ContinuousOn (monopoleMovingCutoffContinuous c) (Ici (0 : ℝ)) := by
  by_cases hc : c = 0
  · subst c
    change ContinuousOn (fun r => bubble r + 0 *
      monopoleInnerRadialContinuous (monopoleQuadraticRadius 0) r) (Ici (0 : ℝ))
    simpa only [zero_mul, add_zero] using
      bubble_contDiff_infty.continuous.continuousOn (s := Ici (0 : ℝ))
  · have hR : 0 < monopoleQuadraticRadius c := by
      unfold monopoleQuadraticRadius
      exact div_pos (by norm_num) (abs_pos.mpr hc)
    exact bubble_contDiff_infty.continuous.continuousOn.add
      ((monopoleInnerRadialContinuous_continuousOn hR).const_mul c)

private theorem nonnegative_integral_bounded_support
    {f : ℝ → ℝ} {R M : ℝ} (hR : 0 < R) (hf : Measurable f)
    (hnonneg : ∀ r, 0 < r → 0 ≤ f r)
    (hbound : ∀ r, 0 < r → f r ≤ M)
    (hzero : ∀ r, R < r → f r = 0) :
    IntegrableOn f (Ioi 0) ∧ (∫ r in Ioi 0, f r) ≤ R * M := by
  let g : ℝ → ℝ := (Ioc (0 : ℝ) R).indicator (fun _ => M)
  have hcore : IntegrableOn (fun _ : ℝ => M) (Ioc (0 : ℝ) R) :=
    (continuous_const.integrableOn_Icc :
      IntegrableOn (fun _ : ℝ => M) (Icc (0 : ℝ) R)).mono_set Ioc_subset_Icc_self
  have hg : IntegrableOn g (Ioi (0 : ℝ)) :=
    (hcore.integrable_indicator measurableSet_Ioc).integrableOn
  have hmajor : ∀ r, 0 < r → ‖f r‖ ≤ g r := by
    intro r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg r hr)]
    by_cases hrR : r ≤ R
    · simpa only [g, Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) R from ⟨hr, hrR⟩)]
        using hbound r hr
    · rw [hzero r (lt_of_not_ge hrR)]
      simp only [g, Set.indicator_of_notMem (show r ∉ Ioc (0 : ℝ) R from
        fun h => hrR h.2), le_refl]
  have hint : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply hg.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hmajor r hr
  refine ⟨hint, ?_⟩
  calc
    (∫ r in Ioi (0 : ℝ), f r) ≤ ∫ r in Ioi (0 : ℝ), g r := by
      apply integral_mono_ae hint hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (le_abs_self (f r)).trans (hmajor r hr)
    _ = R * M := by
      change (∫ r in Ioi (0 : ℝ),
        (Ioc (0 : ℝ) R).indicator (fun _ : ℝ => M) r) = R * M
      rw [setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr Ioc_subset_Ioi_self,
        ← intervalIntegral.integral_of_le hR.le,
        intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]


/-- Actual absolute convergence and the global O(abs(c)) energy bound.
The finite support majorant includes the whole moving transition annulus. -/
private theorem movingCutoff_gradientEnergy_control (c : ℝ) :
    IntegrableOn (monopoleMovingCutoffGradientEnergyDensity c) (Ioi 0) ∧
      (∫ r in Ioi 0, monopoleMovingCutoffGradientEnergyDensity c r) ≤
        monopoleGlobalEnergyConstant * |c| := by
  by_cases hc : c = 0
  · subst c
    have hz : monopoleMovingCutoffGradientEnergyDensity 0 = fun _ => 0 := by
      funext r
      simp [monopoleMovingCutoffGradientEnergyDensity]
    rw [hz]
    simp
  · have habs : 0 < |c| := abs_pos.mpr hc
    have hR : 0 < 8 / |c| := div_pos (by norm_num) habs
    have h := nonnegative_integral_bounded_support hR
      (movingCutoff_energyDensity_measurable c)
      (fun r _ => movingCutoff_energyDensity_nonneg c r)
      (fun r hr => movingCutoff_energyDensity_bound hc hr)
      (fun r hr => by simp only [monopoleMovingCutoffGradientEnergyDensity,
        movingCutoff_derivative_zero_outside hc hr, abs_zero,
        zero_pow (by decide : 2 ≠ 0), mul_zero])
    refine ⟨h.1, h.2.trans_eq ?_⟩
    unfold monopoleGlobalEnergyConstant
    rw [← sq_abs c]
    field_simp [habs.ne']

/-- Absolute convergence of the genuine reduced radial gradient density. -/
theorem monopoleMovingCutoffGradientEnergy_integrable (c : ℝ) :
    IntegrableOn
      (fun r => r ^ 2 * |deriv (monopoleMovingCutoffIncrement c) r| ^ 2)
      (Ioi (0 : ℝ)) :=
  (movingCutoff_gradientEnergy_control c).1

/-- The reduced radial gradient energy is an actual absolutely convergent
integral for every real amplitude, including amplitude zero. -/
def monopoleMovingCutoffGradientEnergy (c : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), monopoleMovingCutoffGradientEnergyDensity c r

theorem monopoleMovingCutoffGradientEnergy_bound (c : ℝ) :
    monopoleMovingCutoffGradientEnergy c ≤ monopoleGlobalEnergyConstant * |c| :=
  (movingCutoff_gradientEnergy_control c).2

/-- The bound holds on both sides of zero, not just along positive amplitudes. -/
theorem monopoleMovingCutoffGradientEnergy_tendsto_zero :
    Tendsto monopoleMovingCutoffGradientEnergy (𝓝 (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero
    (fun c => integral_nonneg (movingCutoff_energyDensity_nonneg c))
    monopoleMovingCutoffGradientEnergy_bound
  simpa only [abs_zero, mul_zero] using
    (continuous_abs.tendsto (0 : ℝ)).const_mul monopoleGlobalEnergyConstant

/-- Square root of the reduced radial gradient energy; the fixed angular
factor is omitted and no three-dimensional lift is inferred by this definition. -/
def monopoleMovingCutoffGradientSeminorm (c : ℝ) : ℝ :=
  Real.sqrt (monopoleMovingCutoffGradientEnergy c)

theorem monopoleMovingCutoffGradientSeminorm_bound (c : ℝ) :
    monopoleMovingCutoffGradientSeminorm c ≤
      Real.sqrt monopoleGlobalEnergyConstant * Real.sqrt |c| := by
  calc
    Real.sqrt (monopoleMovingCutoffGradientEnergy c) ≤
        Real.sqrt (monopoleGlobalEnergyConstant * |c|) :=
      Real.sqrt_le_sqrt (monopoleMovingCutoffGradientEnergy_bound c)
    _ = _ := Real.sqrt_mul monopoleGlobalEnergyConstant_pos.le |c|

theorem monopoleMovingCutoffGradientSeminorm_tendsto_zero :
    Tendsto monopoleMovingCutoffGradientSeminorm (𝓝 (0 : ℝ)) (𝓝 0) := by
  change Tendsto (fun c => Real.sqrt (monopoleMovingCutoffGradientEnergy c))
    (𝓝 (0 : ℝ)) (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp
      monopoleMovingCutoffGradientEnergy_tendsto_zero

/-- Changing the single origin value leaves the genuine positive-radius
increment derivatives unchanged. -/
theorem monopoleMovingCutoffContinuous_increment_deriv_eq (c : ℝ)
    {r : ℝ} (hr : 0 < r) :
    deriv (fun x => monopoleMovingCutoffContinuous c x - bubble x) r =
      deriv (monopoleMovingCutoffIncrement c) r := by
  have he : (fun x => monopoleMovingCutoffContinuous c x - bubble x) =ᶠ[𝓝 r]
      monopoleMovingCutoffIncrement c := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    rw [monopoleMovingCutoffContinuous_eq c hx]
    rfl
  exact he.deriv_eq

/-- Complete actual-cutoff reduced radial energy statement.  Its constant is
constructed from proved profile estimates; no analytic output is a hypothesis.
This auxiliary result does not close the manuscript's three-region matching. -/
theorem monopoleMovingCutoffGlobalEnergy_closed :
    0 < monopoleGlobalEnergyConstant ∧
    (∀ c : ℝ,
      ContinuousOn (monopoleMovingCutoffContinuous c) (Ici (0 : ℝ)) ∧
      monopoleMovingCutoffContinuous c 0 = 1 + c * monopoleRadialOriginValue ∧
      (∀ r, 0 < r → monopoleMovingCutoffContinuous c r =
        monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r) ∧
      (∀ r, 0 < r →
        deriv (fun x => monopoleMovingCutoffContinuous c x - bubble x) r =
          deriv (monopoleMovingCutoffIncrement c) r) ∧
      IntegrableOn
        (fun r => r ^ 2 * |deriv (monopoleMovingCutoffIncrement c) r| ^ 2)
        (Ioi (0 : ℝ)) ∧
      monopoleMovingCutoffGradientEnergy c ≤ monopoleGlobalEnergyConstant * |c| ∧
      monopoleMovingCutoffGradientSeminorm c ≤
        Real.sqrt monopoleGlobalEnergyConstant * Real.sqrt |c|) ∧
    Tendsto monopoleMovingCutoffGradientEnergy (𝓝 (0 : ℝ)) (𝓝 0) ∧
    Tendsto monopoleMovingCutoffGradientSeminorm (𝓝 (0 : ℝ)) (𝓝 0) := by
  refine ⟨monopoleGlobalEnergyConstant_pos, ?_,
    monopoleMovingCutoffGradientEnergy_tendsto_zero,
    monopoleMovingCutoffGradientSeminorm_tendsto_zero⟩
  intro c
  exact ⟨monopoleMovingCutoffContinuous_continuousOn c,
    monopoleMovingCutoffContinuous_origin c,
    (fun r hr => monopoleMovingCutoffContinuous_eq c hr),
    (fun r hr => monopoleMovingCutoffContinuous_increment_deriv_eq c hr),
    monopoleMovingCutoffGradientEnergy_integrable c,
    monopoleMovingCutoffGradientEnergy_bound c,
    monopoleMovingCutoffGradientSeminorm_bound c⟩

end HBL.Modulation.Monopole
