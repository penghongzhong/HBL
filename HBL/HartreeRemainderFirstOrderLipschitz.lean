import HBL.HartreeRemainderFirstOrderQuadratic
import HBL.HartreeFullFirstOrderDifference

/-!
# Complete physical remainder: first-order local Lipschitz control

Exact degree-seven interpolation supplies the small-ball factor. Each of its
eight differences is bounded by the complete first-order source estimate.
The four controlling quantities for an increment are its L∞ and L² sizes and
the L∞ and L² sizes of its actual spatial differential. Thus the X-ball below
is the maximum ball in W¹,² ∩ W¹,∞, on C¹ representatives. Background L² is
not assumed.

The first-order quantity uses the operator norm of the spatial differential;
the weak derivative identity is included explicitly. This estimate does not
assert construction of a constrained propagator or a new accepted manuscript
environment.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators Topology

namespace HBL.RegularRadiation.RemainderFirstOrderLipschitz
open PhysicalExpansion PhysicalInterpolation FirstOrderSource
  FullFirstOrderDifference RemainderFirstOrder

/-- A common bound for the two complete source-difference estimates at the
eight interpolation samples. It depends only on the original background. -/
def remainderFirstOrderLipschitzConstant (κ M L J E : ℝ) : ℝ :=
  let m := M + 7
  let l := L + 7
  let j := 8 * (J + 2401) + 1
  let q := 2 * (E + 49) + 1
  let A := nearMass * m ^ 4 + j ^ 2
  let B := 4 * nearMass * m ^ 3 * l + 2 * (m ^ 2 * j ^ 2 + q ^ 2)
  let CP := 4 * nearMass * m ^ 3 + 8 * m * j
  let CG := nearMass * (4 * m ^ 3 + 16 * m ^ 2 * l) +
    8 * (m + 1) * j + 32 * j * q
  let a := 3 * A * m ^ 2
  let b := 6 * A * m * l + 3 * B * m ^ 2
  let e := 3 * CP * m ^ 2
  3136 * interpolationBound ^ 2 *
    (2 * κ ^ 2 * (a ^ 2 + CP ^ 2 * m ^ 2 * j ^ 2) +
      4 * κ ^ 2 * (a ^ 2 + b ^ 2 + e ^ 2 * q ^ 2 + CG ^ 2 * m ^ 2 * j ^ 2))

private theorem sample_fderiv (w : Space → ℝ) (h : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) (s : ℝ) (x : Space) :
    fderiv ℝ (sampleField w h s) x =
      Complex.ofRealCLM.comp (fderiv ℝ w x) + (s : ℂ) • fderiv ℝ h x :=
  ((Complex.ofRealCLM.hasFDerivAt.comp x
    (hw.differentiable (by norm_num) x).hasFDerivAt).add
    ((hh.differentiable (by norm_num) x).hasFDerivAt.const_mul (s : ℂ))).fderiv

/-- Normalized two-direction form of the complete physical remainder estimate.
All interpolation sample hypotheses follow from the displayed field bounds. -/
theorem physical_remainder_first_order_normalized_difference
    (κ : ℝ) (w : Space → ℝ) (h k : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    (hw4 : Integrable (fun x : Space => |w x| ^ 4))
    (hDw : MemLp (fderiv ℝ w) 2)
    (hh2 : MemLp h 2) (hk2 : MemLp k 2)
    (hDh : MemLp (fderiv ℝ h) 2) (hDk : MemLp (fderiv ℝ k) 2)
    {M L J E t d : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hJ0 : 0 ≤ J) (hE0 : 0 ≤ E)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ∀ᵐ x, ‖h x‖ ≤ 1) (hkb : ∀ᵐ x, ‖k x‖ ≤ 1)
    (hDhb : ∀ᵐ x, ‖fderiv ℝ h x‖ ≤ 1)
    (hDkb : ∀ᵐ x, ‖fderiv ℝ k x‖ ≤ 1)
    (hJ : (∫ x : Space, |w x| ^ 4) ≤ J)
    (hE : (∫ x : Space, ‖fderiv ℝ w x‖ ^ 2) ≤ E)
    (hH : (∫ x : Space, ‖h x‖ ^ 2) ≤ 1)
    (hK : (∫ x : Space, ‖k x‖ ^ 2) ≤ 1)
    (hDH : (∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) ≤ 1)
    (hDK : (∫ x : Space, ‖fderiv ℝ k x‖ ^ 2) ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hd : 0 < d)
    (hδ : ∀ᵐ x, ‖h x - k x‖ ≤ d)
    (hDδ : ∀ᵐ x, ‖fderiv ℝ h x - fderiv ℝ k x‖ ≤ d)
    (hδ2 : (∫ x : Space, ‖h x - k x‖ ^ 2) ≤ d ^ 2)
    (hDδ2 : (∫ x : Space, ‖fderiv ℝ h x - fderiv ℝ k x‖ ^ 2) ≤ d ^ 2) :
    let R := fun x => remainder κ w (fun y => (t : ℂ) * h y) x -
      remainder κ w (fun y => (t : ℂ) * k y) x
    Differentiable ℝ R ∧ MemLp R 2 ∧ MemLp (fderiv ℝ R) 2 ∧
    (∫ x : Space, ‖R x‖ ^ 2) + (∫ x : Space, ‖fderiv ℝ R x‖ ^ 2) ≤
      remainderFirstOrderLipschitzConstant κ M L J E * t ^ 4 * d ^ 2 ∧
    ∀ φ : Space → ℂ, HasCompactSupport φ → ContDiff ℝ 1 φ → ∀ v : Space,
      Integrable (fun x : Space => R x * fderiv ℝ φ x v) ∧
      Integrable (fun x : Space => fderiv ℝ R x v * φ x) ∧
      (∫ x : Space, R x * fderiv ℝ φ x v) =
        -(∫ x : Space, fderiv ℝ R x v * φ x) := by
  dsimp only
  let m := M + 7
  let l := L + 7
  let j := 8 * (J + 2401) + 1
  let q := 2 * (E + 49) + 1
  let A := nearMass * m ^ 4 + j ^ 2
  let B := 4 * nearMass * m ^ 3 * l + 2 * (m ^ 2 * j ^ 2 + q ^ 2)
  let CP := 4 * nearMass * m ^ 3 + 8 * m * j
  let CG := nearMass * (4 * m ^ 3 + 16 * m ^ 2 * l) +
    8 * (m + 1) * j + 32 * j * q
  let a := 3 * A * m ^ 2
  let b := 6 * A * m * l + 3 * B * m ^ 2
  let e := 3 * CP * m ^ 2
  let S0 := 2 * κ ^ 2 * (a ^ 2 + CP ^ 2 * m ^ 2 * j ^ 2)
  let S1 := 4 * κ ^ 2 * (a ^ 2 + b ^ 2 + e ^ 2 * q ^ 2 + CG ^ 2 * m ^ 2 * j ^ 2)
  let F : Fin 8 → Space → ℂ := fun i => sampleField w h (i : ℕ)
  let G : Fin 8 → Space → ℂ := fun i => sampleField w k (i : ℕ)
  let U : Fin 8 → Space → ℂ := fun i x =>
    hartreeNonlinearity κ (F i) x - hartreeNonlinearity κ (G i) x
  let c : Fin 8 → ℂ := fun i => (t : ℂ) ^ 2 * (remainderWeight t i : ℂ)
  let R := fun x => remainder κ w (fun y => (t : ℂ) * h y) x -
    remainder κ w (fun y => (t : ℂ) * k y) x
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have hj : 0 < j := by dsimp [j]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hJj : 8 * (J + 2401) ≤ j ^ 2 := by
    dsimp [j]
    nlinarith [sq_nonneg (8 * (J + 2401))]
  have hEq : 2 * (E + 49) ≤ q ^ 2 := by
    dsimp [q]
    nlinarith [sq_nonneg (2 * (E + 49))]
  have hs (i : Fin 8) : |((i : ℕ) : ℝ)| ≤ 7 := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (show (i : ℕ) ≤ 7 by omega)
  have hsampleF (i : Fin 8) := affine_sample_data w h hw hh hw4 hDw hh2 hDh
    hwb hDwb hhb hDhb hJ hE hH hDH (hs i)
  have hsampleG (i : Fin 8) := affine_sample_data w k hw hk hw4 hDw hk2 hDk
    hwb hDwb hkb hDkb hJ hE hK hDK (hs i)
  have hUdiff (i : Fin 8) : Differentiable ℝ (U i) := by
    obtain ⟨hfc, hf4, hfd, hfb, hfdb, _, _⟩ := hsampleF i
    obtain ⟨hgc, hg4, hgd, hgb, hgdb, _, _⟩ := hsampleG i
    exact (hartree_differential_noncompact κ (F i) hfc hf4 hfd m l hm hl hfb hfdb).1.sub
      (hartree_differential_noncompact κ (G i) hgc hg4 hgd m l hm hl hgb hgdb).1
  have hsource (i : Fin 8) : MemLp (U i) 2 ∧ MemLp (fderiv ℝ (U i)) 2 ∧
      (∫ x : Space, ‖U i x‖ ^ 2) ≤ S0 * (7 * d) ^ 2 ∧
      (∫ x : Space, ‖fderiv ℝ (U i) x‖ ^ 2) ≤ S1 * (7 * d) ^ 2 := by
    obtain ⟨hfc, hf4, hfd, hfb, hfdb, hfj, _⟩ := hsampleF i
    obtain ⟨hgc, hg4, hgd, hgb, hgdb, hgj, hge⟩ := hsampleG i
    let s : ℝ := (i : ℕ)
    have hs0 : 0 ≤ s := Nat.cast_nonneg _
    have hs7 : s ≤ 7 := (le_abs_self s).trans (hs i)
    have hv (x : Space) : F i x - G i x = (s : ℂ) * (h x - k x) := by
      dsimp [F, G, sampleField, s]
      ring
    have hvD (x : Space) : fderiv ℝ (F i) x - fderiv ℝ (G i) x =
        (s : ℂ) • (fderiv ℝ h x - fderiv ℝ k x) := by
      change fderiv ℝ (sampleField w h s) x - fderiv ℝ (sampleField w k s) x = _
      rw [sample_fderiv w h hw hh, sample_fderiv w k hw hk]
      module
    have hfg : MemLp (fun x => F i x - G i x) 2 := by
      have ht := (hh2.sub hk2).const_smul (s : ℂ)
      convert ht using 1
      funext x
      exact hv x
    have hfbδ : ∀ᵐ x, ‖F i x - G i x‖ ≤ 7 * d := by
      filter_upwards [hδ] with x hx
      rw [hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
      exact mul_le_mul hs7 hx (norm_nonneg _) (by norm_num)
    have hfDbδ : ∀ᵐ x, ‖fderiv ℝ (F i) x - fderiv ℝ (G i) x‖ ≤ 7 * d := by
      filter_upwards [hDδ] with x hx
      rw [hvD, norm_smul, Complex.norm_real, Real.norm_of_nonneg hs0]
      exact mul_le_mul hs7 hx (norm_nonneg _) (by norm_num)
    have hfδ2 : (∫ x : Space, ‖F i x - G i x‖ ^ 2) ≤ (7 * d) ^ 2 := by
      simp_rw [hv, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [integral_const_mul]
      calc
        _ ≤ 7 ^ 2 * d ^ 2 := mul_le_mul (pow_le_pow_left₀ hs0 hs7 2) hδ2
          (integral_nonneg fun _ => by positivity) (by norm_num)
        _ = _ := by ring
    have hfDδ2 : (∫ x : Space, ‖fderiv ℝ (F i) x - fderiv ℝ (G i) x‖ ^ 2) ≤
        (7 * d) ^ 2 := by
      simp_rw [hvD, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [integral_const_mul]
      calc
        _ ≤ 7 ^ 2 * d ^ 2 := mul_le_mul (pow_le_pow_left₀ hs0 hs7 2) hDδ2
          (integral_nonneg fun _ => by positivity) (by norm_num)
        _ = _ := by ring
    have hsrc := hartree_first_order_difference_noncompact κ (F i) (G i)
      hfc hgc hf4 hg4 hfd hgd hfg hm hl hj hq (by positivity : 0 < 7 * d)
      hfb hgb hfdb hgdb (hfj.trans hJj) (hgj.trans hJj) (hge.trans hEq)
      hfbδ hfDbδ hfδ2 hfDδ2
    have hdU : fderiv ℝ (U i) = fun x =>
        fderiv ℝ (hartreeNonlinearity κ (F i)) x -
          fderiv ℝ (hartreeNonlinearity κ (G i)) x := by
      funext x
      exact ((hartree_differential_noncompact κ (F i) hfc hf4 hfd m l hm hl hfb hfdb).1 x
        |>.hasFDerivAt.sub
          ((hartree_differential_noncompact κ (G i) hgc hg4 hgd m l hm hl hgb hgdb).1 x).hasFDerivAt).fderiv
    rw [hdU]
    exact ⟨hsrc.1, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2.1⟩
  have hc (i : Fin 8) : ‖c i‖ ≤ t ^ 2 * interpolationBound := by
    dsimp [c]
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ht, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (remainderWeight_bound ht ht1 i) (sq_nonneg t)
  have hB0 : 0 ≤ t ^ 2 * interpolationBound := by
    unfold interpolationBound
    positivity
  have hR : R = fun x => ∑ i : Fin 8, c i • U i x := by
    funext x
    change remainder κ w (fun y => (t : ℂ) * h y) x -
      remainder κ w (fun y => (t : ℂ) * k y) x = _
    rw [physical_remainder_interpolation κ t w h hw.continuous.aestronglyMeasurable
      hw4 hh2 hM (show (0 : ℝ) ≤ 1 by norm_num) hwb hhb x,
      physical_remainder_interpolation κ t w k hw.continuous.aestronglyMeasurable
        hw4 hk2 hM (show (0 : ℝ) ≤ 1 by norm_num) hwb hkb x,
      ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [c, U, F, G]
    ring
  have hRd (x : Space) : HasFDerivAt R
      (∑ i : Fin 8, c i • fderiv ℝ (U i) x) x := by
    rw [hR]
    exact HasFDerivAt.fun_sum (fun i _ => ((hUdiff i) x).hasFDerivAt.const_smul (c i))
  have hDR : fderiv ℝ R = fun x => ∑ i : Fin 8, c i • fderiv ℝ (U i) x := by
    funext x
    exact (hRd x).fderiv
  have hv := eight_L2_combination U c (fun i => (hsource i).1) hB0 hc
    (fun i => (hsource i).2.2.1)
  have hD := eight_L2_combination (fun i => fderiv ℝ (U i)) c
    (fun i => (hsource i).2.1) hB0 hc (fun i => (hsource i).2.2.2)
  have hRv : MemLp R 2 := by rw [hR]; exact hv.1
  have hRD : MemLp (fderiv ℝ R) 2 := by rw [hDR]; exact hD.1
  refine ⟨fun x => (hRd x).differentiableAt, hRv, hRD, ?_, ?_⟩
  · change (∫ x : Space, ‖R x‖ ^ 2) + (∫ x : Space, ‖fderiv ℝ R x‖ ^ 2) ≤ _
    rw [hDR, hR]
    exact (add_le_add hv.2 hD.2).trans_eq (by
      change 64 * (t ^ 2 * interpolationBound) ^ 2 * (S0 * (7 * d) ^ 2) +
        64 * (t ^ 2 * interpolationBound) ^ 2 * (S1 * (7 * d) ^ 2) =
          3136 * interpolationBound ^ 2 * (S0 + S1) * t ^ 4 * d ^ 2
      ring)
  · intro φ hcφ hφ v
    have htφ : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hcφ
    have hDtφ : MemLp (fderiv ℝ φ) 2 :=
      (hφ.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (hcφ.fderiv ℝ)
    have hNv : MemLp (fun x => fderiv ℝ R x v) 2 :=
      hRD.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ v)
    have htv : MemLp (fun x => fderiv ℝ φ x v) 2 :=
      hDtφ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ v)
    have hright := hNv.integrable_mul htφ
    have hleft := hRv.integrable_mul htv
    exact ⟨hleft, hright, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      hright hleft (hRv.integrable_mul htφ)
      (fun x _ => (hRd x).differentiableAt)
      (fun x _ => hφ.differentiable (by norm_num) x)⟩

/-- The maximum ball for the value and spatial-differential L∞ and L²
quantities. The explicit MemLp fields retain actual finite L² membership. -/
structure FirstOrderBall (f : Space → ℂ) (r : ℝ) : Prop where
  value_memLp : MemLp f 2
  derivative_memLp : MemLp (fderiv ℝ f) 2
  value_bound : ∀ᵐ x, ‖f x‖ ≤ r
  derivative_bound : ∀ᵐ x, ‖fderiv ℝ f x‖ ≤ r
  value_square_integral : (∫ x : Space, ‖f x‖ ^ 2) ≤ r ^ 2
  derivative_square_integral : (∫ x : Space, ‖fderiv ℝ f x‖ ^ 2) ≤ r ^ 2

private theorem firstOrderBall_scale (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    {r s : ℝ} (hball : FirstOrderBall f r) (hs : 0 ≤ s) :
    ContDiff ℝ 1 (fun x => (s : ℂ) * f x) ∧
      FirstOrderBall (fun x => (s : ℂ) * f x) (s * r) := by
  let F : Space → ℂ := fun x => (s : ℂ) * f x
  have hfc : ContDiff ℝ 1 F := contDiff_const.mul hf
  have hfd (x : Space) : fderiv ℝ F x = (s : ℂ) • fderiv ℝ f x :=
    ((hf.differentiable (by norm_num) x).hasFDerivAt.const_mul (s : ℂ)).fderiv
  have hD : fderiv ℝ F = fun x => (s : ℂ) • fderiv ℝ f x := funext hfd
  refine ⟨hfc, ?_⟩
  refine ⟨hball.value_memLp.const_smul (s : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · change MemLp (fderiv ℝ F) 2
    rw [hD]
    exact hball.derivative_memLp.const_smul (s : ℂ)
  · filter_upwards [hball.value_bound] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hx hs
  · change ∀ᵐ x, ‖fderiv ℝ F x‖ ≤ s * r
    filter_upwards [hball.derivative_bound] with x hx
    rw [hfd, norm_smul, Complex.norm_real, Real.norm_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hx hs
  · simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs, mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hball.value_square_integral (sq_nonneg s)
  · change (∫ x : Space, ‖fderiv ℝ F x‖ ^ 2) ≤ (s * r) ^ 2
    simp_rw [hfd, norm_smul, Complex.norm_real, Real.norm_of_nonneg hs, mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hball.derivative_square_integral (sq_nonneg s)

/-- Complete physical local Lipschitz estimate on the radius-r X-ball,
including d = 0. Here X is the four-quantity maximum ball `FirstOrderBall`.
Neither background L² nor any assumed nonlinear mapping estimate is used. -/
theorem physical_remainder_first_order_lipschitz
    (κ : ℝ) (w : Space → ℝ) (h k : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    (hw4 : Integrable (fun x : Space => |w x| ^ 4))
    (hDw : MemLp (fderiv ℝ w) 2)
    {M L J E r d : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hJ0 : 0 ≤ J) (hE0 : 0 ≤ E)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hJ : (∫ x : Space, |w x| ^ 4) ≤ J)
    (hE : (∫ x : Space, ‖fderiv ℝ w x‖ ^ 2) ≤ E)
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 ≤ d)
    (hball : FirstOrderBall h r) (kball : FirstOrderBall k r)
    (δball : FirstOrderBall (fun x => h x - k x) d) :
    let R := fun x => remainder κ w h x - remainder κ w k x
    Differentiable ℝ R ∧ MemLp R 2 ∧ MemLp (fderiv ℝ R) 2 ∧
    (∫ x : Space, ‖R x‖ ^ 2) + (∫ x : Space, ‖fderiv ℝ R x‖ ^ 2) ≤
      remainderFirstOrderLipschitzConstant κ M L J E * r ^ 2 * d ^ 2 ∧
    ∀ φ : Space → ℂ, HasCompactSupport φ → ContDiff ℝ 1 φ → ∀ v : Space,
      Integrable (fun x : Space => R x * fderiv ℝ φ x v) ∧
      Integrable (fun x : Space => fderiv ℝ R x v * φ x) ∧
      (∫ x : Space, R x * fderiv ℝ φ x v) =
        -(∫ x : Space, fderiv ℝ R x v * φ x) := by
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · have hkeq : h = k := by
      apply (hh.continuous.ae_eq_iff_eq volume hk.continuous).mp
      filter_upwards [δball.value_bound] with x hx
      apply sub_eq_zero.mp
      exact norm_eq_zero.mp (le_antisymm (hx.trans_eq hd0.symm) (norm_nonneg _))
    subst d
    subst k
    simp
    simpa only [Pi.sub_apply, sub_self] using
      hball.derivative_memLp.sub hball.derivative_memLp
  · let H : Space → ℂ := fun x => ((r⁻¹ : ℝ) : ℂ) * h x
    let K : Space → ℂ := fun x => ((r⁻¹ : ℝ) : ℂ) * k x
    obtain ⟨hHc, hHball⟩ := firstOrderBall_scale h hh hball (inv_nonneg.mpr hr.le)
    obtain ⟨hKc, hKball⟩ := firstOrderBall_scale k hk kball (inv_nonneg.mpr hr.le)
    rw [inv_mul_cancel₀ hr.ne'] at hHball hKball
    have hHK : (fun x => H x - K x) =
        (fun x => ((r⁻¹ : ℝ) : ℂ) * (h x - k x)) := by
      funext x
      dsimp [H, K]
      ring
    have hδball : FirstOrderBall (fun x => H x - K x) (d / r) := by
      rw [hHK]
      have hv := (firstOrderBall_scale (fun x => h x - k x) (hh.sub hk) δball
        (inv_nonneg.mpr hr.le)).2
      simpa only [div_eq_mul_inv, mul_comm] using hv
    have hDHK : fderiv ℝ (fun x => H x - K x) =
        (fun x => fderiv ℝ H x - fderiv ℝ K x) := by
      funext x
      exact ((hHc.differentiable (by norm_num) x).hasFDerivAt.sub
        (hKc.differentiable (by norm_num) x).hasFDerivAt).fderiv
    have hDδ : ∀ᵐ x, ‖fderiv ℝ H x - fderiv ℝ K x‖ ≤ d / r := by
      simpa only [hDHK] using hδball.derivative_bound
    have hDδ2 : (∫ x : Space, ‖fderiv ℝ H x - fderiv ℝ K x‖ ^ 2) ≤ (d / r) ^ 2 := by
      simpa only [hDHK] using hδball.derivative_square_integral
    have hv := physical_remainder_first_order_normalized_difference κ w H K hw hHc hKc
      hw4 hDw hHball.value_memLp hKball.value_memLp hHball.derivative_memLp hKball.derivative_memLp
      hM hL hJ0 hE0 hwb hDwb hHball.value_bound hKball.value_bound
      hHball.derivative_bound hKball.derivative_bound hJ hE
      (by simpa only [one_pow] using hHball.value_square_integral)
      (by simpa only [one_pow] using hKball.value_square_integral)
      (by simpa only [one_pow] using hHball.derivative_square_integral)
      (by simpa only [one_pow] using hKball.derivative_square_integral) hr.le hr1
      (div_pos hdpos hr) hδball.value_bound hDδ hδball.value_square_integral hDδ2
    have hrestore (f : Space → ℂ) :
        (fun x => (r : ℂ) * (((r⁻¹ : ℝ) : ℂ) * f x)) = f := by
      funext x
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne',
        Complex.ofReal_one, one_mul]
    change (let R := fun x => remainder κ w (fun y => (r : ℂ) * H y) x -
      remainder κ w (fun y => (r : ℂ) * K y) x
      Differentiable ℝ R ∧ MemLp R 2 ∧ MemLp (fderiv ℝ R) 2 ∧
      (∫ x : Space, ‖R x‖ ^ 2) + (∫ x : Space, ‖fderiv ℝ R x‖ ^ 2) ≤
        remainderFirstOrderLipschitzConstant κ M L J E * r ^ 4 * (d / r) ^ 2 ∧ _) at hv
    dsimp only [H, K] at hv
    rw [hrestore h, hrestore k] at hv
    have hscale : remainderFirstOrderLipschitzConstant κ M L J E * r ^ 4 * (d / r) ^ 2 =
        remainderFirstOrderLipschitzConstant κ M L J E * r ^ 2 * d ^ 2 := by
      field_simp
    rw [hscale] at hv
    exact hv

#print axioms remainderFirstOrderLipschitzConstant
#print axioms FirstOrderBall
#print axioms physical_remainder_first_order_normalized_difference
#print axioms physical_remainder_first_order_lipschitz

end HBL.RegularRadiation.RemainderFirstOrderLipschitz
