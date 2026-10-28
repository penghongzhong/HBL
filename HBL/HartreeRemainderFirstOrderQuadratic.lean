import HBL.HartreeRemainderInterpolation
import HBL.HartreeFirstOrderSource

/-!
# Complete physical remainder: first-order quadratic control

All eight source samples are derived from the same field assumptions. The
background is C1, L4 and bounded, with L2/bounded differential; background
L2 is not required. The normalized perturbation and its differential are
L2/bounded by one. Exact interpolation then retains t^2 for the entire
seventh-order remainder, including its actual spatial differential.

This file does not construct the constrained evolution, close higher Sobolev
estimates, or assert a newly accepted original manuscript environment.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Topology

namespace HBL.RegularRadiation.RemainderFirstOrder
open PhysicalExpansion PhysicalInterpolation FirstOrderSource

private theorem fourth_sum (a b : ℝ) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith only [sq_nonneg (a - b)]
  have h2 := pow_le_pow_left₀ (sq_nonneg (a + b)) h1 2
  nlinarith only [h2, sq_nonneg (a ^ 2 - b ^ 2)]

private theorem eight_square (a b c d e f g h : ℝ) :
    (a + b + c + d + e + f + g + h) ^ 2 ≤
      8 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2) := by
  nlinarith only [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
    sq_nonneg (a-e), sq_nonneg (a-f), sq_nonneg (a-g), sq_nonneg (a-h),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (b-e), sq_nonneg (b-f),
    sq_nonneg (b-g), sq_nonneg (b-h), sq_nonneg (c-d), sq_nonneg (c-e),
    sq_nonneg (c-f), sq_nonneg (c-g), sq_nonneg (c-h), sq_nonneg (d-e),
    sq_nonneg (d-f), sq_nonneg (d-g), sq_nonneg (d-h), sq_nonneg (e-f),
    sq_nonneg (e-g), sq_nonneg (e-h), sq_nonneg (f-g), sq_nonneg (f-h),
    sq_nonneg (g-h)]

private theorem eight_norm_square {E : Type*} [NormedAddCommGroup E]
    (v : Fin 8 → E) : ‖∑ i, v i‖ ^ 2 ≤ 8 * ∑ i, ‖v i‖ ^ 2 := by
  have ht := norm_sum_le (s := Finset.univ) v
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hb : (∑ i : Fin 8, ‖v i‖) ^ 2 ≤ 8 * ∑ i : Fin 8, ‖v i‖ ^ 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      eight_square ‖v 0‖ ‖v 1‖ ‖v 2‖ ‖v 3‖ ‖v 4‖ ‖v 5‖ ‖v 6‖ ‖v 7‖
  exact hs.trans hb

private theorem eight_L2_combination {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : Fin 8 → Space → E) (c : Fin 8 → ℂ)
    (hF : ∀ i, MemLp (F i) 2) {B S : ℝ} (hB : 0 ≤ B)
    (hc : ∀ i, ‖c i‖ ≤ B)
    (hS : ∀ i, (∫ x : Space, ‖F i x‖ ^ 2) ≤ S) :
    MemLp (fun x => ∑ i, c i • F i x) 2 ∧
      (∫ x : Space, ‖∑ i, c i • F i x‖ ^ 2) ≤ 64 * B ^ 2 * S := by
  have hm := ((hF 0).const_smul (c 0)).add
    (((hF 1).const_smul (c 1)).add (((hF 2).const_smul (c 2)).add
      (((hF 3).const_smul (c 3)).add (((hF 4).const_smul (c 4)).add
        (((hF 5).const_smul (c 5)).add (((hF 6).const_smul (c 6)).add
          ((hF 7).const_smul (c 7))))))))
  have hmem : MemLp (fun x => ∑ i, c i • F i x) 2 := by
    simpa [Fin.sum_univ_succ, Pi.smul_apply, Pi.add_apply] using hm
  have hi := (hF 0).norm.integrable_sq.add
    ((hF 1).norm.integrable_sq.add ((hF 2).norm.integrable_sq.add
      ((hF 3).norm.integrable_sq.add ((hF 4).norm.integrable_sq.add
        ((hF 5).norm.integrable_sq.add ((hF 6).norm.integrable_sq.add
          (hF 7).norm.integrable_sq))))))
  have hsum : Integrable (fun x : Space => ∑ i : Fin 8, ‖F i x‖ ^ 2) := by
    simpa [Fin.sum_univ_succ, Pi.add_apply] using hi
  have hb (x : Space) : ‖∑ i, c i • F i x‖ ^ 2 ≤
      (8 * B ^ 2) * ∑ i : Fin 8, ‖F i x‖ ^ 2 := by
    calc
      _ ≤ 8 * ∑ i, ‖c i • F i x‖ ^ 2 := eight_norm_square _
      _ ≤ 8 * ∑ i : Fin 8, B ^ 2 * ‖F i x‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hc i) 2) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hI := integral_mono_ae hmem.norm.integrable_sq
    (hsum.const_mul (8 * B ^ 2)) (Filter.Eventually.of_forall hb)
  rw [integral_const_mul,
    integral_finsetSum _ (fun (i : Fin 8) _ => (hF i).norm.integrable_sq)] at hI
  have htotal : (∑ i : Fin 8, ∫ x : Space, ‖F i x‖ ^ 2) ≤ 8 * S := by
    calc
      _ ≤ ∑ _i : Fin 8, S := Finset.sum_le_sum (fun i _ => hS i)
      _ = _ := by simp
  exact ⟨hmem, hI.trans ((mul_le_mul_of_nonneg_left htotal (by positivity)).trans_eq (by ring))⟩

/-- All sample constants depend only on the original background bounds. -/
def remainderFirstOrderConstant (κ M L J E : ℝ) : ℝ :=
  let m := M + 7
  let l := L + 7
  let j := 8 * (J + 2401)
  let e := 2 * (E + 49)
  let A := nearMass * m ^ 4 + j
  let B := 4 * nearMass * m ^ 3 * l + 2 * (m ^ 2 * j + e)
  64 * interpolationBound ^ 2 *
    (κ ^ 2 * A ^ 2 * m ^ 2 * j +
      2 * κ ^ 2 * (B ^ 2 * m ^ 2 * j + 9 * A ^ 2 * m ^ 4 * e))

private theorem affine_sample_data
    (w : Space → ℝ) (h : Space → ℂ) (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h)
    (hw4 : Integrable (fun x : Space => |w x| ^ 4))
    (hDw : MemLp (fderiv ℝ w) 2) (hh2 : MemLp h 2) (hDh : MemLp (fderiv ℝ h) 2)
    {M L J E s : ℝ} (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ∀ᵐ x, ‖h x‖ ≤ 1) (hDhb : ∀ᵐ x, ‖fderiv ℝ h x‖ ≤ 1)
    (hJ : (∫ x : Space, |w x| ^ 4) ≤ J) (hE : (∫ x : Space, ‖fderiv ℝ w x‖ ^ 2) ≤ E)
    (hH : (∫ x : Space, ‖h x‖ ^ 2) ≤ 1) (hDH : (∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) ≤ 1)
    (hs : |s| ≤ 7) :
    ContDiff ℝ 1 (sampleField w h s) ∧
    Integrable (fun x : Space => ‖sampleField w h s x‖ ^ 4) ∧
    MemLp (fderiv ℝ (sampleField w h s)) 2 ∧
    (∀ᵐ x, ‖sampleField w h s x‖ ≤ M + 7) ∧
    (∀ᵐ x, ‖fderiv ℝ (sampleField w h s) x‖ ≤ L + 7) ∧
    (∫ x : Space, ‖sampleField w h s x‖ ^ 4) ≤ 8 * (J + 2401) ∧
    (∫ x : Space, ‖fderiv ℝ (sampleField w h s) x‖ ^ 2) ≤ 2 * (E + 49) := by
  let f := sampleField w h s
  have hfc : ContDiff ℝ 1 f :=
    (Complex.ofRealCLM.contDiff.comp hw).add (contDiff_const.mul hh)
  have hv (x : Space) : ‖f x‖ ≤ |w x| + 7 * ‖h x‖ := by
    apply (norm_add_le (w x : ℂ) ((s : ℂ) * h x)).trans
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul] using
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hs (norm_nonneg (h x)))
  have hd (x : Space) : fderiv ℝ f x =
      Complex.ofRealCLM.comp (fderiv ℝ w x) + (s : ℂ) • fderiv ℝ h x :=
    ((Complex.ofRealCLM.hasFDerivAt.comp x (hw.differentiable (by norm_num) x).hasFDerivAt).add
      ((hh.differentiable (by norm_num) x).hasFDerivAt.const_mul (s : ℂ))).fderiv
  have hdv (x : Space) : ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ w x‖ + 7 * ‖fderiv ℝ h x‖ := by
    have hlift : ‖Complex.ofRealCLM.comp (fderiv ℝ w x)‖ ≤ ‖fderiv ℝ w x‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro v
      simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
        Complex.norm_real] using (fderiv ℝ w x).le_opNorm v
    rw [hd]
    apply (norm_add_le _ _).trans
    apply add_le_add hlift
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
  have hhsq : ∀ᵐ x, ‖h x‖ ^ 4 ≤ ‖h x‖ ^ 2 := by
    filter_upwards [hhb] with x hx
    have hx2 : ‖h x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (h x)]
    nlinarith only [mul_le_mul_of_nonneg_right hx2 (sq_nonneg ‖h x‖)]
  have hh4 : Integrable (fun x : Space => ‖h x‖ ^ 4) :=
    hh2.norm.integrable_sq.mono' (hh.continuous.aestronglyMeasurable.norm.pow 4)
      (hhsq.mono fun x hx => by simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ ‖h x‖ ^ 4)] using hx)
  have hH4 : (∫ x : Space, ‖h x‖ ^ 4) ≤ 1 :=
    (integral_mono_ae hh4 hh2.norm.integrable_sq hhsq).trans hH
  have hv4 (x : Space) : ‖f x‖ ^ 4 ≤ 8 * (|w x| ^ 4 + 2401 * ‖h x‖ ^ 4) := by
    apply (pow_le_pow_left₀ (norm_nonneg _) (hv x) 4).trans
    simpa only [mul_pow, show (7 : ℝ) ^ 4 = 2401 by norm_num] using
      fourth_sum |w x| (7 * ‖h x‖)
  have hmajor4 := (hw4.add (hh4.const_mul 2401)).const_mul 8
  have hfi : Integrable (fun x : Space => ‖f x‖ ^ 4) :=
    hmajor4.mono' (hfc.continuous.aestronglyMeasurable.norm.pow 4)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Pi.add_apply, Real.norm_of_nonneg (by positivity : 0 ≤ ‖f x‖ ^ 4)] using hv4 x)
  have hd2 (x : Space) : ‖fderiv ℝ f x‖ ^ 2 ≤
      2 * (‖fderiv ℝ w x‖ ^ 2 + 49 * ‖fderiv ℝ h x‖ ^ 2) := by
    apply (pow_le_pow_left₀ (norm_nonneg _) (hdv x) 2).trans
    nlinarith only [sq_nonneg (‖fderiv ℝ w x‖ - 7 * ‖fderiv ℝ h x‖)]
  have hdmajor := (hDw.norm.integrable_sq.add (hDh.norm.integrable_sq.const_mul 49)).const_mul 2
  have hDmeas := (hfc.continuous_fderiv (by norm_num)).aestronglyMeasurable
  have hdi : Integrable (fun x : Space => ‖fderiv ℝ f x‖ ^ 2) :=
    hdmajor.mono' (hDmeas.norm.pow 2) (Filter.Eventually.of_forall fun x => by
      simpa only [Pi.add_apply, Real.norm_of_nonneg (sq_nonneg _)] using hd2 x)
  refine ⟨hfc, hfi, (memLp_two_iff_integrable_sq_norm hDmeas).2 hdi, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hwb, hhb] with x hx hhx
    nlinarith [hv x]
  · filter_upwards [hDwb, hDhb] with x hx hhx
    nlinarith [hdv x]
  · have hi := integral_mono_ae hfi hmajor4 (Filter.Eventually.of_forall hv4)
    simp only [Pi.add_apply] at hi
    rw [integral_const_mul, integral_add hw4 (hh4.const_mul 2401), integral_const_mul] at hi
    nlinarith only [hi, hJ, hH4]
  · have hi := integral_mono_ae hdi hdmajor (Filter.Eventually.of_forall hd2)
    simp only [Pi.add_apply] at hi
    rw [integral_const_mul, integral_add hDw.norm.integrable_sq
      (hDh.norm.integrable_sq.const_mul 49), integral_const_mul] at hi
    nlinarith only [hi, hE, hDH]

/-- Complete actual seventh-order remainder, including its weak spatial
 differential, has a uniform quadratic bound on each normalized direction.
The displayed constant is independent of that direction and of t in [0,1].
All sample conditions are derived; no background L2 hypothesis is used. -/
theorem physical_remainder_first_order_quadratic
    (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h)
    (hw4 : Integrable (fun x : Space => |w x| ^ 4))
    (hDw : MemLp (fderiv ℝ w) 2) (hh2 : MemLp h 2) (hDh : MemLp (fderiv ℝ h) 2)
    {M L J E t : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hJ0 : 0 ≤ J) (hE0 : 0 ≤ E)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ∀ᵐ x, ‖h x‖ ≤ 1) (hDhb : ∀ᵐ x, ‖fderiv ℝ h x‖ ≤ 1)
    (hJ : (∫ x : Space, |w x| ^ 4) ≤ J) (hE : (∫ x : Space, ‖fderiv ℝ w x‖ ^ 2) ≤ E)
    (hH : (∫ x : Space, ‖h x‖ ^ 2) ≤ 1) (hDH : (∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    let R := remainder κ w (fun x => (t : ℂ) * h x)
    Differentiable ℝ R ∧ MemLp R 2 ∧ MemLp (fderiv ℝ R) 2 ∧
    (∫ x : Space, ‖R x‖ ^ 2) + (∫ x : Space, ‖fderiv ℝ R x‖ ^ 2) ≤
      remainderFirstOrderConstant κ M L J E * t ^ 4 ∧
    ∀ φ : Space → ℂ, HasCompactSupport φ → ContDiff ℝ 1 φ → ∀ v : Space,
      Integrable (fun x : Space => R x * fderiv ℝ φ x v) ∧
      Integrable (fun x : Space => fderiv ℝ R x v * φ x) ∧
      (∫ x : Space, R x * fderiv ℝ φ x v) = -(∫ x : Space, fderiv ℝ R x v * φ x) := by
  dsimp only
  let m := M + 7
  let l := L + 7
  let j := 8 * (J + 2401)
  let e := 2 * (E + 49)
  let A := nearMass * m ^ 4 + j
  let B := 4 * nearMass * m ^ 3 * l + 2 * (m ^ 2 * j + e)
  let S0 := κ ^ 2 * A ^ 2 * m ^ 2 * j
  let S1 := 2 * κ ^ 2 * (B ^ 2 * m ^ 2 * j + 9 * A ^ 2 * m ^ 4 * e)
  let F : Fin 8 → Space → ℂ := fun i => sampleField w h (i : ℕ)
  let N : Fin 8 → Space → ℂ := fun i => hartreeNonlinearity κ (F i)
  let c : Fin 8 → ℂ := fun i => (t : ℂ) ^ 2 * (remainderWeight t i : ℂ)
  let R := remainder κ w (fun x => (t : ℂ) * h x)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have hnear := regularRadiationKernel_checks.2.1
  have hsamples (i : Fin 8) := affine_sample_data w h hw hh hw4 hDw hh2 hDh
    hwb hDwb hhb hDhb hJ hE hH hDH
    (show |((i : ℕ) : ℝ)| ≤ 7 by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (show (i : ℕ) ≤ 7 by omega))
  have hsource (i : Fin 8) : Differentiable ℝ (N i) ∧ MemLp (N i) 2 ∧
      MemLp (fderiv ℝ (N i)) 2 ∧
      (∫ x : Space, ‖N i x‖ ^ 2) ≤ S0 ∧
      (∫ x : Space, ‖fderiv ℝ (N i) x‖ ^ 2) ≤ S1 := by
    obtain ⟨hfc, hf4, hfd, hfb, hfdb, hfj, hfe⟩ := hsamples i
    have hsrc := hartree_first_order_source_noncompact κ (F i) hfc hf4 hfd m l hm hl hfb hfdb
    have hdiff := (hartree_differential_noncompact κ (F i) hfc hf4 hfd m l hm hl hfb hfdb).1
    have hJi : 0 ≤ ∫ x : Space, ‖F i x‖ ^ 4 := integral_nonneg (fun _ => by positivity)
    have hEi : 0 ≤ ∫ x : Space, ‖fderiv ℝ (F i) x‖ ^ 2 := integral_nonneg (fun _ => by positivity)
    have hAi : nearMass * m ^ 4 + (∫ x : Space, ‖F i x‖ ^ 4) ≤ A := by
      dsimp [A]; exact add_le_add le_rfl hfj
    have hBi : nearMass * (4 * m ^ 3 * l) +
        2 * (m ^ 2 * (∫ x : Space, ‖F i x‖ ^ 4) + ∫ x : Space, ‖fderiv ℝ (F i) x‖ ^ 2) ≤ B := by
      dsimp [B]
      nlinarith only [mul_le_mul_of_nonneg_left hfj (sq_nonneg m), hfe]
    refine ⟨hdiff, hsrc.1, hsrc.2.1, ?_, ?_⟩
    · apply hsrc.2.2.1.trans
      dsimp [S0]
      gcongr
    · apply hsrc.2.2.2.trans
      dsimp [S1]
      gcongr
  have hc (i : Fin 8) : ‖c i‖ ≤ t ^ 2 * interpolationBound := by
    dsimp [c]
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ht, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (remainderWeight_bound ht ht1 i) (sq_nonneg t)
  have hB0 : 0 ≤ t ^ 2 * interpolationBound := by
    unfold interpolationBound; positivity
  have hR : R = fun x => ∑ i : Fin 8, c i • N i x := by
    funext x
    rw [physical_remainder_interpolation κ t w h hw.continuous.aestronglyMeasurable
      hw4 hh2 hM (show (0 : ℝ) ≤ 1 by norm_num) hwb hhb x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [c, N, F]
    simp only [smul_eq_mul]
    ring
  have hRd (x : Space) : HasFDerivAt R (∑ i : Fin 8, c i • fderiv ℝ (N i) x) x := by
    rw [hR]
    exact HasFDerivAt.fun_sum (fun i _ => ((hsource i).1 x).hasFDerivAt.const_smul (c i))
  have hDR : fderiv ℝ R = fun x => ∑ i : Fin 8, c i • fderiv ℝ (N i) x := by
    funext x
    exact (hRd x).fderiv
  have hv := eight_L2_combination N c (fun i => (hsource i).2.1) hB0 hc
    (fun i => (hsource i).2.2.2.1)
  have hd := eight_L2_combination (fun i => fderiv ℝ (N i)) c
    (fun i => (hsource i).2.2.1) hB0 hc (fun i => (hsource i).2.2.2.2)
  have hRv : MemLp R 2 := by rw [hR]; exact hv.1
  have hRD : MemLp (fderiv ℝ R) 2 := by rw [hDR]; exact hd.1
  refine ⟨fun x => (hRd x).differentiableAt, hRv, hRD, ?_, ?_⟩
  · rw [hR, hDR]
    exact (add_le_add hv.2 hd.2).trans_eq (by
      dsimp [remainderFirstOrderConstant, S0, S1, A, B, m, l, j, e]
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
      (fun x _ => (hRd x).differentiableAt) (fun x _ => hφ.differentiable (by norm_num) x)⟩

#print axioms remainderFirstOrderConstant
#print axioms physical_remainder_first_order_quadratic
end HBL.RegularRadiation.RemainderFirstOrder
