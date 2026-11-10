import HBL.TypeIIDynamicSelection.ActualHartreeBackwardVolterraParameterDifference
import Mathlib.Tactic

/-!
# Source-faithful normalized backward-overlap C2 stability

The only source sizes below are suprema of the ACTUAL original Kummer
operator evaluated on the fields. No envelope, inverse norm, decay order,
or rate is an input. Both source-controlled zero-jet inverses are the
existing radial weak-term absorption theorem on [1/2,1].

After the physical substitution y=L*x, the effective scale is a/L.
Thus these bounds isolate the genuine moving-radius source transport
instead of differentiating a moving Kummer basis. They do NOT prove the
full moving Hartree source budget or either unproved original environment.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Profile.Kummer

/-- An actual source norm on the one fixed normalized physical interval. -/
def actualHartreeNormalizedSourceSup (G : ℝ → ℂ) : ℝ :=
  sSup ((fun x : ℝ => ‖G x‖) '' Icc (1 / 2 : ℝ) 1)

private theorem sourceSup_bounds (G : ℝ → ℂ)
    (hG : ContinuousOn G (Icc (1 / 2 : ℝ) 1)) :
    0 ≤ actualHartreeNormalizedSourceSup G ∧
      ∀ x ∈ Icc (1 / 2 : ℝ) 1,
        ‖G x‖ ≤ actualHartreeNormalizedSourceSup G := by
  have hb : BddAbove ((fun x : ℝ => ‖G x‖) '' Icc (1 / 2 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hG.norm
  have hbound (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
      ‖G x‖ ≤ actualHartreeNormalizedSourceSup G :=
    le_csSup hb ⟨x, hx, rfl⟩
  exact ⟨(norm_nonneg _).trans (hbound (1 / 2) (by norm_num)), hbound⟩

private theorem local_Kummer_sub
    (mu theta a r : ℝ) (hr : 0 < r) (e1 e2 : ℝ → ℂ)
    (he1 : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ e1 x)
    (he2 : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ e2 x)
    (he1two : DifferentiableAt ℝ (deriv e1) r)
    (he2two : DifferentiableAt ℝ (deriv e2) r) :
    DifferentiableAt ℝ (deriv (fun x => e1 x - e2 x)) r ∧
    actualMatchedScaledKummerApply mu theta a (fun x => e1 x - e2 x) r =
      actualMatchedScaledKummerApply mu theta a e1 r -
        actualMatchedScaledKummerApply mu theta a e2 r := by
  have hfirst (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y => e1 y - e2 y) (deriv e1 x - deriv e2 x) x :=
    (he1 x hx).hasDerivAt.sub (he2 x hx).hasDerivAt
  have hnear : deriv (fun x => e1 x - e2 x) =ᶠ[𝓝 r]
      (fun x => deriv e1 x - deriv e2 x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hfirst x hx).deriv
  have hsecond :=
    (he1two.hasDerivAt.sub he2two.hasDerivAt).congr_of_eventuallyEq hnear
  refine ⟨hsecond.differentiableAt, ?_⟩
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecond.deriv, (hfirst r hr).deriv]
  simp only [Complex.real_smul]
  ring

/-- Quantitative C2 stability of the ORIGINAL zero-jet radial Kummer
fields. The displayed source norms are computed from their original
operator evaluations; no source majorant or Lipschitz bound is assumed. -/
theorem actual_Hartree_normalized_original_source_C2_stability
    (mu1 theta1 mu2 theta2 a1 a2 : ℝ) (e1 e2 : ℝ → ℂ)
    (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hsmall1 : 4 * ((1 + ‖frozenZeroCoeff mu1 theta1‖) / a1 ^ 2) ≤ 1)
    (hsmall2 : 4 * ((1 + ‖frozenZeroCoeff mu2 theta2‖) / a2 ^ 2) ≤ 1)
    (he1 : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ e1 x)
    (he2 : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ e2 x)
    (he1two : ∀ x ∈ Icc (1 / 2 : ℝ) 1, DifferentiableAt ℝ (deriv e1) x)
    (he2two : ∀ x ∈ Icc (1 / 2 : ℝ) 1, DifferentiableAt ℝ (deriv e2) x)
    (hzero1 : e1 1 = 0) (hdzero1 : deriv e1 1 = 0)
    (hzero2 : e2 1 = 0) (hdzero2 : deriv e2 1 = 0)
    (hG1 : ContinuousOn (actualMatchedScaledKummerApply mu1 theta1 a1 e1)
      (Icc (1 / 2 : ℝ) 1))
    (hG2 : ContinuousOn (actualMatchedScaledKummerApply mu2 theta2 a2 e2)
      (Icc (1 / 2 : ℝ) 1)) :
    let G1 := actualMatchedScaledKummerApply mu1 theta1 a1 e1
    let G2 := actualMatchedScaledKummerApply mu2 theta2 a2 e2
    let kdiff := (a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹
    let zdiff := ((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
      ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2
    let B := actualHartreeNormalizedSourceSup (fun x => G1 x - G2 x) +
      2 * (|kdiff| + ‖zdiff‖) * actualHartreeNormalizedSourceSup G2
    let d := fun x => e1 x - e2 x
    ∀ x ∈ Icc (1 / 2 : ℝ) 1,
      ‖d x‖ ≤ 2 * B ∧ ‖deriv d x‖ ≤ 4 * B ∧
        ‖deriv (deriv d) x‖ ≤ 18 * B := by
  dsimp only
  let G1 := actualMatchedScaledKummerApply mu1 theta1 a1 e1
  let G2 := actualMatchedScaledKummerApply mu2 theta2 a2 e2
  let kdiff := (a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹
  let zdiff := ((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
    ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2
  let A2 := actualHartreeNormalizedSourceSup G2
  let Ad := actualHartreeNormalizedSourceSup (fun x => G1 x - G2 x)
  let B := Ad + 2 * (|kdiff| + ‖zdiff‖) * A2
  let d : ℝ → ℂ := fun x => e1 x - e2 x
  have hS2 := sourceSup_bounds G2 hG2
  have hSd := sourceSup_bounds (fun x => G1 x - G2 x) (hG1.sub hG2)
  have hA2 : 0 ≤ A2 := hS2.1
  have hAd : 0 ≤ Ad := hSd.1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hSub : Icc (1 / 2 : ℝ) (2 * (1 / 2)) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le (by norm_num) hx.1
  have hsmall1' : 16 * (1 / 2 : ℝ) ^ 2 *
      ((1 + ‖frozenZeroCoeff mu1 theta1‖) / a1 ^ 2) ≤ 1 := by
    convert hsmall1 using 1 <;> ring
  have hsmall2' : 16 * (1 / 2 : ℝ) ^ 2 *
      ((1 + ‖frozenZeroCoeff mu2 theta2‖) / a2 ^ 2) ≤ 1 := by
    convert hsmall2 using 1 <;> ring
  obtain ⟨C, _hC, hgain⟩ := actual_Hartree_matched_scaled_Kummer_shell_gain
  have hE2 (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
      ‖e2 x‖ ≤ 2 * A2 ∧ ‖deriv e2 x‖ ≤ 4 * A2 := by
    have hh := hgain mu2 theta2 a2 e2 (Ioi 0) (1 / 2) A2 1
      isOpen_Ioi hSub ha2 (by norm_num) hA2 hsmall2' (by norm_num)
      he2
      (fun y hy => he2two y (by norm_num at hy ⊢; exact hy))
      hzero2 hdzero2
      (fun y hy => hS2.2 y (by norm_num at hy ⊢; exact hy))
      x (by norm_num at hx ⊢; exact hx)
    have hv := hh.2.1
    have hdv := hh.2.2.1
    norm_num at hv hdv
    exact ⟨hv, hdv⟩
  have hd : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ d x := by
    intro x hx
    exact (he1 x hx).sub (he2 x hx)
  have hdd : ∀ x ∈ Icc (1 / 2 : ℝ) 1, DifferentiableAt ℝ (deriv d) x := by
    intro x hx
    exact (local_Kummer_sub mu1 theta1 a1 x
      (lt_of_lt_of_le (by norm_num) hx.1) e1 e2 he1 he2
      (he1two x hx) (he2two x hx)).1
  have hd0 : d 1 = 0 := by simp [d, hzero1, hzero2]
  have hdd0 : deriv d 1 = 0 := by
    have h := ((he1 1 (by norm_num)).hasDerivAt.sub
      (he2 1 (by norm_num)).hasDerivAt).deriv
    change deriv (e1 - e2) 1 = 0
    simpa only [hdzero1, hdzero2, sub_self] using h
  have hsource (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
      ‖actualMatchedScaledKummerApply mu1 theta1 a1 d x‖ ≤ B := by
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    have hlinear := (local_Kummer_sub mu1 theta1 a1 x hx0 e1 e2
      he1 he2 (he1two x hx) (he2two x hx)).2
    have hcoeff := actual_Hartree_original_Kummer_coefficient_difference
      mu1 theta1 mu2 theta2 a1 a2 x e2
    have hEq : actualMatchedScaledKummerApply mu1 theta1 a1 d x =
        (G1 x - G2 x) -
          kdiff • (Complex.I * (x : ℂ) / 2 * deriv e2 x) - zdiff * e2 x := by
      dsimp only [d, G1, G2, kdiff, zdiff]
      rw [hlinear]
      linear_combination -hcoeff
    have hcx : ‖Complex.I * (x : ℂ) / 2‖ = x / 2 := by
      simp [abs_of_pos hx0]
    have hc : ‖Complex.I * (x : ℂ) / 2‖ ≤ (1 / 2 : ℝ) := by
      rw [hcx]
      linarith [hx.2]
    have hj := hE2 x hx
    have htransport :
        ‖kdiff • (Complex.I * (x : ℂ) / 2 * deriv e2 x)‖ ≤
          |kdiff| * ((1 / 2) * (4 * A2)) := by
      rw [norm_smul, Real.norm_eq_abs, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hc hj.2 (norm_nonneg _) (by norm_num)) (abs_nonneg _)
    have hzero : ‖zdiff * e2 x‖ ≤ ‖zdiff‖ * (2 * A2) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hj.1 (norm_nonneg _)
    rw [hEq]
    calc
      _ ≤ (‖G1 x - G2 x‖ +
          ‖kdiff • (Complex.I * (x : ℂ) / 2 * deriv e2 x)‖) +
          ‖zdiff * e2 x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (Ad + |kdiff| * ((1 / 2) * (4 * A2))) + ‖zdiff‖ * (2 * A2) :=
        add_le_add (add_le_add (hSd.2 x hx) htransport) hzero
      _ = B := by dsimp [B]; ring
  intro x hx
  have hh := hgain mu1 theta1 a1 d (Ioi 0) (1 / 2) B 1
    isOpen_Ioi hSub ha1 (by norm_num) hB hsmall1' (by norm_num) hd
    (fun y hy => hdd y (by norm_num at hy ⊢; exact hy)) hd0 hdd0
    (fun y hy => hsource y (by norm_num at hy ⊢; exact hy))
    x (by norm_num at hx ⊢; exact hx)
  have hv : ‖d x‖ ≤ 2 * B := by
    have hv0 := hh.2.1
    norm_num at hv0
    exact hv0
  have hder : ‖deriv d x‖ ≤ 4 * B := by
    have hdv0 := hh.2.2.1
    norm_num at hdv0
    exact hdv0
  have hlap : ‖complexRadialLaplacian d x‖ ≤ 2 * B := hh.1
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hc : ‖(2 : ℂ) / (x : ℂ)‖ ≤ (4 : ℝ) := by
    have hxnorm : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hx0]
    rw [norm_div, hxnorm]
    norm_num
    apply (div_le_iff₀ hx0).2
    linarith [hx.1]
  have hs : deriv (deriv d) x = complexRadialLaplacian d x -
      (2 : ℂ) / (x : ℂ) * deriv d x := by
    unfold complexRadialLaplacian
    ring
  refine ⟨hv, hder, ?_⟩
  rw [hs]
  calc
    _ ≤ ‖complexRadialLaplacian d x‖ +
        ‖(2 : ℂ) / (x : ℂ) * deriv d x‖ := norm_sub_le _ _
    _ ≤ 2 * B + 4 * (4 * B) := by
      rw [norm_mul]
      exact add_le_add hlap (mul_le_mul hc hder (norm_nonneg _) (by norm_num))
    _ = 18 * B := by ring

end HBL.TypeIIDynamicSelection
