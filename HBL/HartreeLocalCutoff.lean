import HBL.HartreeQuarticGradient
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Native removal of the compact-core approximation premise

Construct expanding smooth cutoffs, then exploit the inverse-square kernel
outside twice a fixed observation ball. Source errors need not converge in
L-infinity on the whole space: their actual convolutions converge uniformly
on every fixed ball. The limiting derivative is obtained from these native
cutoffs, not from an assumed approximation sequence.

The final density theorem assumes C1 regularity, L1 integrability of the
density and its differential, and their displayed uniform bounds. Its
quartic specialization derives those density assumptions from field data.
This does not construct the constrained Hartree evolution or the main orbit.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology

namespace HBL.RegularRadiation.LocalCutoff

open SpatialCompletion QuarticGradient

private def radius (n : ℕ) : ℝ := (n : ℝ) + 1

private theorem radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  positivity

private theorem cutoff_family :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ χ : ℕ → Space → ℝ,
      (∀ n, ContDiff ℝ 1 (χ n)) ∧
      (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ n x, ‖x‖ < 2 * radius n → χ n x = 1) ∧
      (∀ n x, ‖fderiv ℝ (χ n) x‖ ≤ B) := by
  let b : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : ContDiff ℝ 1 (b : Space → ℝ) := b.contDiff
  obtain ⟨B, hB⟩ := (hb.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv ℝ)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let c : ℕ → ℝ := fun n => (2 * radius n)⁻¹
  have hcpos (n : ℕ) : 0 < c n := inv_pos.mpr (mul_pos (by norm_num) (radius_pos n))
  have hc1 (n : ℕ) : c n ≤ 1 := by
    apply (inv_le_one₀ (mul_pos (by norm_num) (radius_pos n))).2
    dsimp [radius]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hceq (n : ℕ) : c n * (2 * radius n) = 1 :=
    inv_mul_cancel₀ (ne_of_gt (mul_pos (by norm_num) (radius_pos n)))
  let χ : ℕ → Space → ℝ := fun n x => b (c n • x)
  have hχ (n : ℕ) : ContDiff ℝ 1 (χ n) := by
    have hs : ContDiff ℝ 1 (fun y : Space => c n • y) :=
      (c n • ContinuousLinearMap.id ℝ Space).contDiff
    exact hb.comp hs
  have hχc (n : ℕ) : HasCompactSupport (χ n) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Space) (4 * radius n))
    intro x hx
    by_contra hout
    have hxlarge : 4 * radius n ≤ ‖x‖ := by
      have h : 4 * radius n < ‖x‖ := by
        simpa only [mem_closedBall_zero_iff, not_le] using hout
      exact h.le
    have hcx : 2 ≤ ‖c n • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hcpos n).le]
      have ht := mul_le_mul_of_nonneg_left hxlarge (hcpos n).le
      nlinarith [hceq n]
    have hz : χ n x = 0 := b.zero_of_le_dist (by simpa [b, dist_zero_right] using hcx)
    exact hx hz
  have hχone (n : ℕ) (x : Space) (hx : ‖x‖ < 2 * radius n) : χ n x = 1 := by
    apply b.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff]
    change ‖c n • x‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (hcpos n).le]
    exact (mul_le_mul_of_nonneg_left hx.le (hcpos n).le).trans_eq (hceq n)
  refine ⟨B, hB0, χ, hχ, hχc, ?_, hχone, ?_⟩
  · intro n x
    exact ⟨b.nonneg, b.le_one⟩
  · intro n x
    have hd := ((hb.differentiable (by norm_num)) (c n • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul (c n))
    have he : fderiv ℝ (χ n) x =
        (fderiv ℝ (b : Space → ℝ) (c n • x)).comp
          (c n • ContinuousLinearMap.id ℝ Space) := hd.fderiv
    rw [he]
    have hscale : ‖c n • ContinuousLinearMap.id ℝ Space‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      change ‖c n • v‖ ≤ 1 * ‖v‖
      rw [norm_smul, Real.norm_of_nonneg (hcpos n).le]
      exact mul_le_mul_of_nonneg_right (hc1 n) (norm_nonneg v)
    calc
      _ ≤ ‖fderiv ℝ (b : Space → ℝ) (c n • x)‖ *
          ‖c n • ContinuousLinearMap.id ℝ Space‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * 1 := mul_le_mul (hB _) hscale (norm_nonneg _) hB0
      _ = B := mul_one B

private theorem kernel_tail_bound (R : ℝ) (hR : 0 < R) (x y : Space)
    (hx : ‖x‖ ≤ R) (hy : 2 * R ≤ ‖y‖) : kernel (x - y) ≤ (R ^ 2)⁻¹ := by
  have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc
      ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
  have hdist : R ≤ ‖x - y‖ := by linarith
  have hs := pow_le_pow_left₀ hR.le hdist 2
  simpa only [kernel, one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hR) hs

private theorem tail_integral_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : Space → E) (hf : Integrable f) (R : ℝ) (hR : 0 < R)
    (hz : ∀ y, ‖y‖ < 2 * R → f y = 0) (x : Space) (hx : ‖x‖ ≤ R) :
    Integrable (fun y : Space => (kernel (x - y) : ℂ) • f y) ∧
      ‖∫ y : Space, (kernel (x - y) : ℂ) • f y‖ ≤
        (R ^ 2)⁻¹ * (∫ y : Space, ‖f y‖) := by
  have hk : Measurable (fun y : Space => (kernel (x - y) : ℂ)) := by
    unfold kernel
    fun_prop
  have hbound : ∀ y : Space, ‖(kernel (x - y) : ℂ) • f y‖ ≤ (R ^ 2)⁻¹ * ‖f y‖ := by
    intro y
    by_cases hy : ‖y‖ < 2 * R
    · rw [hz y hy]
      simp
    · rw [norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by unfold kernel; positivity : 0 ≤ kernel (x - y))]
      exact mul_le_mul_of_nonneg_right (kernel_tail_bound R hR x y hx (le_of_not_gt hy))
        (norm_nonneg _)
  have hmajor := hf.norm.const_mul ((R ^ 2)⁻¹)
  have hi : Integrable (fun y : Space => (kernel (x - y) : ℂ) • f y) :=
    hmajor.mono' (hk.aestronglyMeasurable.smul hf.aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y : Space, ‖(kernel (x - y) : ℂ) • f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : Space, (R ^ 2)⁻¹ * ‖f y‖ :=
      integral_mono_ae hi.norm hmajor (Filter.Eventually.of_forall hbound)
    _ = _ := integral_const_mul _ _

private theorem uniform_on_ball {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → Space → E) (g : Space → E) (C : ℝ)
    (hb : ∀ n x, ‖x‖ ≤ radius n → ‖f n x - g x‖ ≤ ((radius n) ^ 2)⁻¹ * C)
    (R : ℝ) : TendstoUniformlyOn f g atTop (ball (0 : Space) R) := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => ((radius n) ^ 2)⁻¹ * C) atTop (𝓝 0) := by
    simpa only [radius, one_div, inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      using (ht.pow 2).mul_const C
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro e he
  filter_upwards [eventually_ge_atTop N, (tendsto_order.1 hlim).2 e he] with n hn hne
  intro x hx
  have hxn : ‖x‖ ≤ radius n := by
    have hxr : ‖x‖ < R := by simpa only [mem_ball_zero_iff] using hx
    have hnr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [radius]
    linarith
  calc
    dist (g x) (f n x) = ‖f n x - g x‖ := by rw [dist_comm, dist_eq_norm]
    _ ≤ ((radius n) ^ 2)⁻¹ * C := hb n x hxn
    _ < e := hne

/-- The actual noncompact derivative formula. No approximants, decay at infinity,
or derivative-of-potential identities are input hypotheses. -/
theorem potential_hasFDerivAt_noncompact
    (ρ : Space → ℂ) (hρ : ContDiff ℝ 1 ρ)
    (hi : Integrable ρ) (hDi : Integrable (fderiv ℝ ρ))
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hb0 : ∀ᵐ y : Space, ‖ρ y‖ ≤ M0)
    (hb1 : ∀ᵐ y : Space, ‖fderiv ℝ ρ y‖ ≤ M1) (x : Space) :
    HasFDerivAt (potential ρ) (gradientPotential (fderiv ℝ ρ) x) x := by
  obtain ⟨B, hB, χ, hχ, hχc, hχb, hχone, hχD⟩ := cutoff_family
  let q : ℕ → Space → ℂ := fun n y => χ n y • ρ y
  have hq (n : ℕ) : ContDiff ℝ 1 (q n) := (hχ n).smul hρ
  have hqc (n : ℕ) : HasCompactSupport (q n) := by
    apply HasCompactSupport.of_support_subset_isCompact (hχc n).isCompact
    intro y hy
    by_contra hn
    exact hy (by change χ n y • ρ y = 0; rw [image_eq_zero_of_notMem_tsupport hn, zero_smul])
  have hqi (n : ℕ) : Integrable (q n) :=
    (hq n).continuous.integrable_of_hasCompactSupport (hqc n)
  have hqDi (n : ℕ) : Integrable (fderiv ℝ (q n)) :=
    ((hq n).continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport ((hqc n).fderiv ℝ)
  have hχnorm (n : ℕ) (y : Space) : ‖χ n y‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hχb n y).1]
    exact (hχb n y).2
  have hχsub (n : ℕ) (y : Space) : ‖χ n y - 1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hχb n y).1, (hχb n y).2]
  have hqbound (n : ℕ) (y : Space) : ‖q n y‖ ≤ ‖ρ y‖ := by
    change ‖χ n y • ρ y‖ ≤ _
    rw [norm_smul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχnorm n y) (norm_nonneg _)
  have he0 (n : ℕ) (y : Space) : ‖q n y - ρ y‖ ≤ ‖ρ y‖ := by
    have he : q n y - ρ y = (χ n y - 1) • ρ y := by simp [q, sub_smul]
    rw [he, norm_smul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχsub n y) (norm_nonneg _)
  have hqd (n : ℕ) (y : Space) : fderiv ℝ (q n) y =
      χ n y • fderiv ℝ ρ y + (fderiv ℝ (χ n) y).smulRight (ρ y) :=
    fderiv_fun_smul ((hχ n).differentiable (by norm_num) y) (hρ.differentiable (by norm_num) y)
  have hqDbound (n : ℕ) (y : Space) :
      ‖fderiv ℝ (q n) y‖ ≤ ‖fderiv ℝ ρ y‖ + B * ‖ρ y‖ := by
    rw [hqd]
    calc
      _ ≤ ‖χ n y • fderiv ℝ ρ y‖ + ‖(fderiv ℝ (χ n) y).smulRight (ρ y)‖ := norm_add_le _ _
      _ = ‖χ n y‖ * ‖fderiv ℝ ρ y‖ + ‖fderiv ℝ (χ n) y‖ * ‖ρ y‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ 1 * ‖fderiv ℝ ρ y‖ + B * ‖ρ y‖ := add_le_add
        (mul_le_mul_of_nonneg_right (hχnorm n y) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hχD n y) (norm_nonneg _))
      _ = _ := by ring
  have he1 (n : ℕ) (y : Space) :
      ‖fderiv ℝ (q n) y - fderiv ℝ ρ y‖ ≤ ‖fderiv ℝ ρ y‖ + B * ‖ρ y‖ := by
    have he : fderiv ℝ (q n) y - fderiv ℝ ρ y =
        (χ n y - 1) • fderiv ℝ ρ y + (fderiv ℝ (χ n) y).smulRight (ρ y) := by
      rw [hqd]
      ext v
      change χ n y • (fderiv ℝ ρ y v) + (fderiv ℝ (χ n) y v) • ρ y -
        fderiv ℝ ρ y v =
        (χ n y - 1) • (fderiv ℝ ρ y v) + (fderiv ℝ (χ n) y v) • ρ y
      rw [sub_smul, one_smul]
      abel
    rw [he]
    calc
      _ ≤ ‖(χ n y - 1) • fderiv ℝ ρ y‖ + ‖(fderiv ℝ (χ n) y).smulRight (ρ y)‖ := norm_add_le _ _
      _ = ‖χ n y - 1‖ * ‖fderiv ℝ ρ y‖ + ‖fderiv ℝ (χ n) y‖ * ‖ρ y‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ 1 * ‖fderiv ℝ ρ y‖ + B * ‖ρ y‖ := add_le_add
        (mul_le_mul_of_nonneg_right (hχsub n y) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hχD n y) (norm_nonneg _))
      _ = _ := by ring
  have hbq (n : ℕ) : ∀ᵐ y : Space, ‖q n y‖ ≤ M0 :=
    hb0.mono (fun y hy => (hqbound n y).trans hy)
  have hbqD (n : ℕ) : ∀ᵐ y : Space, ‖fderiv ℝ (q n) y‖ ≤ M1 + B * M0 := by
    filter_upwards [hb0, hb1] with y hy hdy
    exact (hqDbound n y).trans (add_le_add hdy (mul_le_mul_of_nonneg_left hy hB))
  have hz0 (n : ℕ) (y : Space) (hy : ‖y‖ < 2 * radius n) : q n y - ρ y = 0 := by
    simp only [q, hχone n y hy, one_smul, sub_self]
  have hz1 (n : ℕ) (y : Space) (hy : ‖y‖ < 2 * radius n) :
      fderiv ℝ (q n) y - fderiv ℝ ρ y = 0 := by
    have he : q n =ᶠ[𝓝 y] ρ := by
      filter_upwards [(isOpen_ball.mem_nhds (show y ∈ ball (0 : Space) (2 * radius n) by
        simpa only [mem_ball_zero_iff] using hy))] with z hz
      change χ n z • ρ z = ρ z
      rw [hχone n z (by simpa only [mem_ball_zero_iff] using hz), one_smul]
    rw [he.fderiv_eq, sub_self]
  have hI0 (n : ℕ) : (∫ y : Space, ‖q n y - ρ y‖) ≤ ∫ y : Space, ‖ρ y‖ :=
    integral_mono_ae ((hqi n).sub hi).norm hi.norm (Filter.Eventually.of_forall (he0 n))
  have hI1 (n : ℕ) : (∫ y : Space, ‖fderiv ℝ (q n) y - fderiv ℝ ρ y‖) ≤
      (∫ y : Space, ‖fderiv ℝ ρ y‖) + B * (∫ y : Space, ‖ρ y‖) := by
    have ht := integral_mono_ae ((hqDi n).sub hDi).norm (hDi.norm.add (hi.norm.const_mul B))
      (Filter.Eventually.of_forall (he1 n))
    simp only [Pi.add_apply, Pi.sub_apply] at ht
    rw [integral_add hDi.norm (hi.norm.const_mul B), integral_const_mul] at ht
    exact ht
  have hv (n : ℕ) (z : Space) (hz : ‖z‖ ≤ radius n) :
      ‖potential (q n) z - potential ρ z‖ ≤
        ((radius n) ^ 2)⁻¹ * (∫ y : Space, ‖ρ y‖) := by
    have ht := (tail_integral_bound (fun y => q n y - ρ y) ((hqi n).sub hi)
      (radius n) (radius_pos n) (hz0 n) z hz).2
    have he : (∫ y : Space, (kernel (z - y) : ℂ) • (q n y - ρ y)) =
        potential (q n) z - potential ρ z := by
      simp_rw [smul_eq_mul, mul_sub]
      exact integral_sub (potential_bound (q n) (hqi n) M0 hM0 (hbq n) z).1
        (potential_bound ρ hi M0 hM0 hb0 z).1
    rw [he] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (hI0 n) (by positivity))
  have hg (n : ℕ) (z : Space) (hz : ‖z‖ ≤ radius n) :
      ‖gradientPotential (fderiv ℝ (q n)) z - gradientPotential (fderiv ℝ ρ) z‖ ≤
        ((radius n) ^ 2)⁻¹ *
          ((∫ y : Space, ‖fderiv ℝ ρ y‖) + B * (∫ y : Space, ‖ρ y‖)) := by
    have ht := (tail_integral_bound (fun y => fderiv ℝ (q n) y - fderiv ℝ ρ y)
      ((hqDi n).sub hDi) (radius n) (radius_pos n) (hz1 n) z hz).2
    have he : (∫ y : Space, (kernel (z - y) : ℂ) •
        (fderiv ℝ (q n) y - fderiv ℝ ρ y)) =
        gradientPotential (fderiv ℝ (q n)) z - gradientPotential (fderiv ℝ ρ) z := by
      simp_rw [smul_sub]
      exact integral_sub
        (gradientPotential_bound (fderiv ℝ (q n)) (hqDi n) (M1 + B * M0)
          (by positivity) (hbqD n) z).1
        (gradientPotential_bound (fderiv ℝ ρ) hDi M1 hM1 hb1 z).1
    rw [he] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (hI1 n) (by positivity))
  have hvlim := uniform_on_ball (fun n => potential (q n)) (potential ρ)
    (∫ y : Space, ‖ρ y‖) hv (‖x‖ + 1)
  have hglim := uniform_on_ball (fun n => gradientPotential (fderiv ℝ (q n)))
    (gradientPotential (fderiv ℝ ρ))
    ((∫ y : Space, ‖fderiv ℝ ρ y‖) + B * (∫ y : Space, ‖ρ y‖)) hg (‖x‖ + 1)
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hglim
    (fun n z _ => potential_core_gradient (q n) (hqc n) (hq n)
      (M1 + B * M0) (by positivity) (hbqD n) z)
    (fun z hz => hvlim.tendsto_at hz)
    (show x ∈ ball (0 : Space) (‖x‖ + 1) by simp only [mem_ball_zero_iff]; linarith)

/-- Actual quartic Hartree potential derivative with the old approximation
hypotheses completely discharged. No field L2 or compact support is required. -/
theorem quarticPotential_hasFDerivAt_noncompact
    (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (h4 : Integrable (fun y : Space => ‖f y‖ ^ 4))
    (hd : MemLp (fderiv ℝ f) 2)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfb : ∀ᵐ y : Space, ‖f y‖ ≤ M)
    (hdb : ∀ᵐ y : Space, ‖fderiv ℝ f y‖ ≤ L) (x : Space) :
    HasFDerivAt (potential (quarticDensity f))
      (gradientPotential (fderiv ℝ (quarticDensity f)) x) x := by
  obtain ⟨hi, hDi, _, hb⟩ := quarticDensity_gradient_source f hf h4 hd M L hM hL hfb hdb
  have hb0 : ∀ᵐ y : Space, ‖quarticDensity f y‖ ≤ M ^ 4 := by
    filter_upwards [hfb] with y hy
    simpa only [quarticDensity, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using
      pow_le_pow_left₀ (norm_nonneg _) hy 4
  exact potential_hasFDerivAt_noncompact (quarticDensity f) (quarticDensity_contDiff f hf)
    hi hDi (M ^ 4) (4 * M ^ 3 * L) (by positivity) (by positivity) hb0 hb x

#print axioms potential_hasFDerivAt_noncompact
#print axioms quarticPotential_hasFDerivAt_noncompact

end HBL.RegularRadiation.LocalCutoff
