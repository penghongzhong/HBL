import HBL.UnstableShootingKernel

/-!
Independent stable scalar initial-value problem. The coefficient is a
primitive continuous real path. The actual Hartree spectral coefficient
is NOT assumed constructed by this file. No abstract evolution operator
or uniqueness premise is used to define the solution.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Shooting

/-- Actual solution of y'=-a*y with y(s0)=alpha. -/
def stableInitialSolution (a : ℝ → ℝ) (s0 alpha s : ℝ) : ℝ :=
  alpha * unstableShootingKernel a s0 s

private theorem stable_initial_derivative
    {a : ℝ → ℝ} (ha : Continuous a) (s0 alpha s : ℝ) :
    HasDerivAt (stableInitialSolution a s0 alpha)
      (-a s * stableInitialSolution a s0 alpha s) s := by
  have h := (unstableShootingKernel_hasDerivAt_right ha s0 s).const_mul alpha
  apply h.congr_deriv
  dsimp [stableInitialSolution]
  ring

private theorem stable_initial_bound
    {a : ℝ → ℝ} {s0 e alpha s : ℝ} (ha : Continuous a)
    (hrate : ∀ t, s0 ≤ t → e ≤ a t) (hs : s0 ≤ s) :
    |stableInitialSolution a s0 alpha s| ≤
      |alpha| * Real.exp (-e * (s - s0)) := by
  rw [stableInitialSolution, abs_mul,
    abs_of_pos (unstableShootingKernel_pos a s0 s)]
  exact mul_le_mul_of_nonneg_left
    (unstableShootingKernel_le_exp hs ha.continuousOn
      (fun t ht => hrate t ht.1)) (abs_nonneg alpha)

private theorem stable_initial_unique
    {a y : ℝ → ℝ} {s0 alpha : ℝ} (ha : Continuous a)
    (hy : ∀ t, s0 ≤ t → HasDerivAt y (-a t * y t) t)
    (hinit : y s0 = alpha) :
    ∀ s, s0 ≤ s → y s = stableInitialSolution a s0 alpha s := by
  intro s hs
  let v : ℝ → ℝ := fun t => Real.exp (∫ u in s0..t, a u) * y t
  have hd (t : ℝ) (ht : s0 ≤ t) : HasDerivAt v 0 t := by
    have hi := intervalIntegral.integral_hasDerivAt_right
      (ha.intervalIntegrable s0 t)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
    have hm := hi.exp.mul (hy t ht)
    apply hm.congr_deriv
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := s0) (b := s)
    (fun t ht => hd t (by rw [uIcc_of_le hs] at ht; exact ht.1))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume s0 s)
  have hv : v s = v s0 := by
    apply sub_eq_zero.mp
    simpa only [intervalIntegral.integral_zero] using hFTC.symm
  have hv' : Real.exp (∫ u in s0..s, a u) * y s = alpha := by
    simpa [v, hinit] using hv
  have hcancel : Real.exp (-(∫ u in s0..s, a u)) *
      Real.exp (∫ u in s0..s, a u) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    y s = Real.exp (-(∫ u in s0..s, a u)) *
        (Real.exp (∫ u in s0..s, a u) * y s) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = Real.exp (-(∫ u in s0..s, a u)) * alpha := by rw [hv']
    _ = stableInitialSolution a s0 alpha s := by
      unfold stableInitialSolution unstableShootingKernel
      ring

private theorem stable_initial_limit
    {a : ℝ → ℝ} {s0 e alpha : ℝ} (ha : Continuous a) (he : 0 < e)
    (hrate : ∀ t, s0 ≤ t → e ≤ a t) :
    Tendsto (stableInitialSolution a s0 alpha) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => e * (t - s0)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b / e + s0)] with t ht
    have hb : b / e ≤ t - s0 := by linarith
    simpa only [mul_comm] using (div_le_iff₀ he).mp hb
  have hexp : Tendsto (fun t : ℝ => |alpha| * Real.exp (-e * (t - s0)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).const_mul |alpha|
  apply squeeze_zero_norm' _ hexp
  filter_upwards [eventually_ge_atTop s0] with s hs
  simpa only [Real.norm_eq_abs] using stable_initial_bound ha hrate hs

private theorem stable_initial_difference
    {a b : ℝ → ℝ} {s0 s e D alpha beta : ℝ}
    (ha : Continuous a) (hb : Continuous b) (hs : s0 ≤ s)
    (hA : ∀ t, s0 ≤ t → e ≤ a t)
    (hB : ∀ t, s0 ≤ t → e ≤ b t)
    (hD : ∀ t, s0 ≤ t → |a t - b t| ≤ D) :
    |stableInitialSolution a s0 alpha s - stableInitialSolution b s0 beta s| ≤
      (|alpha - beta| + |beta| * D * (s - s0)) * Real.exp (-e * (s - s0)) := by
  have hk := unstableShootingKernel_le_exp hs ha.continuousOn
    (fun t ht => hA t ht.1)
  have hkd := unstableShootingKernel_difference_bound hs ha.continuousOn hb.continuousOn
    (fun t ht => hA t ht.1) (fun t ht => hB t ht.1) (fun t ht => hD t ht.1)
  have hid : stableInitialSolution a s0 alpha s - stableInitialSolution b s0 beta s =
      (alpha - beta) * unstableShootingKernel a s0 s +
      beta * (unstableShootingKernel a s0 s - unstableShootingKernel b s0 s) := by
    unfold stableInitialSolution
    ring
  rw [hid]
  calc
    |(alpha - beta) * unstableShootingKernel a s0 s +
        beta * (unstableShootingKernel a s0 s - unstableShootingKernel b s0 s)| ≤
        |(alpha - beta) * unstableShootingKernel a s0 s| +
        |beta * (unstableShootingKernel a s0 s - unstableShootingKernel b s0 s)| := abs_add_le _ _
    _ ≤ |alpha - beta| * Real.exp (-e * (s - s0)) +
        |beta| * (D * (s - s0) * Real.exp (-e * (s - s0))) := by
      rw [abs_mul, abs_mul, abs_of_pos (unstableShootingKernel_pos a s0 s)]
      exact add_le_add (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hkd (abs_nonneg _))
    _ = _ := by ring

/-- Full stable scalar initial-value environment, including uniqueness,
exponential decay and coefficient/initial-data comparison. Uniqueness is
for classical solutions whose ODE holds at all t>=s0, including s0.
This is independent of the unresolved physical spectral decomposition. -/
theorem stableInitialPropagation_certified
    (a : ℝ → ℝ) (s0 alpha e : ℝ) (ha : Continuous a) (he : 0 < e)
    (hrate : ∀ t, s0 ≤ t → e ≤ a t) :
    stableInitialSolution a s0 alpha s0 = alpha ∧
    Continuous (stableInitialSolution a s0 alpha) ∧
    (∀ s, HasDerivAt (stableInitialSolution a s0 alpha)
      (-a s * stableInitialSolution a s0 alpha s) s) ∧
    (∀ s, s0 ≤ s → |stableInitialSolution a s0 alpha s| ≤
      |alpha| * Real.exp (-e * (s - s0))) ∧
    Tendsto (stableInitialSolution a s0 alpha) atTop (𝓝 0) ∧
    (∀ y : ℝ → ℝ, (∀ t, s0 ≤ t → HasDerivAt y (-a t * y t) t) →
      y s0 = alpha → ∀ s, s0 ≤ s → y s = stableInitialSolution a s0 alpha s) ∧
    (∀ (b : ℝ → ℝ) (beta D : ℝ), Continuous b →
      (∀ t, s0 ≤ t → e ≤ b t) →
      (∀ t, s0 ≤ t → |a t - b t| ≤ D) →
      ∀ s, s0 ≤ s →
      |stableInitialSolution a s0 alpha s - stableInitialSolution b s0 beta s| ≤
        (|alpha - beta| + |beta| * D * (s - s0)) * Real.exp (-e * (s - s0))) := by
  refine ⟨?_, ?_, stable_initial_derivative ha s0 alpha,
    (fun s hs => stable_initial_bound ha hrate hs),
    stable_initial_limit ha he hrate,
    (fun y hy hy0 => stable_initial_unique ha hy hy0), ?_⟩
  · simp [stableInitialSolution]
  · exact continuous_const.mul (unstableShootingKernel_continuous_right ha s0)
  · intro b beta D hb hB hD s hs
    exact stable_initial_difference ha hb hs hrate hB hD

end HBL.Shooting
