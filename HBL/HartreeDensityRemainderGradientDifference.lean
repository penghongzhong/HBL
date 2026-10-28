import HBL.HartreeDensityRemainderGradient
import HBL.HartreeDensityDifferenceBounds

/-!
# First-order two-perturbation control of the physical density remainder

Reuse the exact density differential and the actual noncompact convolution.
Keep one perturbation radius and one difference radius after differentiation.
The background is real C1 and bounded together with its differential; no
background L2/L4 or compact support is imposed. This is the density part of
the Hartree remainder, not the full seventh-order remainder or the PDE flow.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Topology
namespace HBL.RegularRadiation.PhysicalExpansion
open SpatialCompletion

/-- Explicit coefficient independent of the difference radius. -/
def densityGradientDifferenceConstant (M L r : ℝ) : ℝ :=
  8 * L * (3 * M + 2 * r) +
    4 * (M ^ 2 + (2 * M + r) * (M + r)) +
    4 * (M ^ 2 + (2 * M + r) * r + (2 * M + 2 * r) * (M + r))

private def inc (a : ℝ) (z : ℂ) : ℝ := 2 * a * z.re + ‖z‖ ^ 2
private def incD (a b : ℝ) (z H : ℂ) : ℝ :=
  b * z.re + a * H.re + inner ℝ z H
private def grad (a b : ℝ) (z H : ℂ) : ℝ :=
  4 * a * b * ‖z‖ ^ 2 + 4 * a ^ 2 * inner ℝ z H + 4 * inc a z * incD a b z H

private theorem sqdiff (z v : ℂ) :
    |‖z‖ ^ 2 - ‖v‖ ^ 2| ≤ (‖z‖ + ‖v‖) * ‖z - v‖ := by
  rw [show ‖z‖ ^ 2 - ‖v‖ ^ 2 = (‖z‖ - ‖v‖) * (‖z‖ + ‖v‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg v))]
  exact (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z v)
    (add_nonneg (norm_nonneg z) (norm_nonneg v))).trans_eq (by ring)

private theorem inc_bound (a : ℝ) (z : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (ha : |a| ≤ M) (hz : ‖z‖ ≤ r) :
    |inc a z| ≤ (2 * M + r) * ‖z‖ := by
  have h1 : |2 * a * z.re| ≤ 2 * M * ‖z‖ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (by linarith : 2 * |a| ≤ 2 * M)
      (Complex.abs_re_le_norm z) (abs_nonneg _) (by positivity)
  have h2 : ‖z‖ ^ 2 ≤ r * ‖z‖ := by
    nlinarith only [mul_le_mul_of_nonneg_right hz (norm_nonneg z)]
  calc
    _ ≤ |2 * a * z.re| + |‖z‖ ^ 2| := abs_add_le _ _
    _ ≤ 2 * M * ‖z‖ + r * ‖z‖ := by
      rw [abs_of_nonneg (sq_nonneg ‖z‖)]
      exact add_le_add h1 h2
    _ = _ := by ring

private theorem inc_difference (a : ℝ) (z v : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (ha : |a| ≤ M) (hz : ‖z‖ ≤ r) (hv : ‖v‖ ≤ r) :
    |inc a z - inc a v| ≤ (2 * M + 2 * r) * ‖z - v‖ := by
  have hre : |z.re - v.re| ≤ ‖z - v‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - v)
  have he : inc a z - inc a v =
      2 * a * (z.re - v.re) + (‖z‖ ^ 2 - ‖v‖ ^ 2) := by unfold inc; ring
  rw [he]
  calc
    _ ≤ |2 * a * (z.re - v.re)| + |‖z‖ ^ 2 - ‖v‖ ^ 2| := abs_add_le _ _
    _ ≤ 2 * M * ‖z - v‖ + (‖z‖ + ‖v‖) * ‖z - v‖ := by
      apply add_le_add _ (sqdiff z v)
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul (by linarith : 2 * |a| ≤ 2 * M) hre (abs_nonneg _) (by positivity)
    _ ≤ 2 * M * ‖z - v‖ + (2 * r) * ‖z - v‖ := by gcongr; linarith
    _ = _ := by ring

private theorem inner_difference (z v H K : ℂ) {e q t : ℝ}
    (hHK : ‖H - K‖ ≤ e * t) (hK : ‖K‖ ≤ q * t) :
    |inner ℝ z H - inner ℝ v K| ≤ (‖z‖ * e + ‖z - v‖ * q) * t := by
  have he : inner ℝ z H - inner ℝ v K =
      inner ℝ z (H - K) + inner ℝ (z - v) K := by
    rw [inner_sub_right, inner_sub_left]
    ring
  have hi (x y : ℂ) : |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x y
  rw [he]
  calc
    _ ≤ |inner ℝ z (H - K)| + |inner ℝ (z - v) K| := abs_add_le _ _
    _ ≤ ‖z‖ * ‖H - K‖ + ‖z - v‖ * ‖K‖ := add_le_add (hi _ _) (hi _ _)
    _ ≤ ‖z‖ * (e * t) + ‖z - v‖ * (q * t) := by gcongr
    _ = _ := by ring

private theorem incD_bound (a b : ℝ) (v K : ℂ) {M L r q t : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (_hq : 0 ≤ q) (ht : 0 ≤ t)
    (ha : |a| ≤ M) (hb : |b| ≤ L * t) (hv : ‖v‖ ≤ r) (hK : ‖K‖ ≤ q * t) :
    |incD a b v K| ≤ (L * ‖v‖ + (M + r) * q) * t := by
  have hi : |inner ℝ v K| ≤ ‖v‖ * ‖K‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v K
  calc
    _ ≤ |b * v.re| + |a * K.re| + |inner ℝ v K| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (L * t) * ‖v‖ + M * (q * t) + r * (q * t) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul hb (Complex.abs_re_le_norm v) (abs_nonneg _) (by positivity))
        (mul_le_mul ha ((Complex.abs_re_le_norm K).trans hK) (abs_nonneg _) hM))
        (hi.trans (mul_le_mul hv hK (norm_nonneg _) (le_trans (norm_nonneg v) hv)))
    _ = _ := by ring

private theorem incD_difference (a b : ℝ) (z v H K : ℂ) {M L r e q t : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (he : 0 ≤ e) (ht : 0 ≤ t)
    (ha : |a| ≤ M) (hb : |b| ≤ L * t) (hz : ‖z‖ ≤ r)
    (hHK : ‖H - K‖ ≤ e * t) (hK : ‖K‖ ≤ q * t) :
    |incD a b z H - incD a b v K| ≤
      (L * ‖z - v‖ + (M + r) * e + ‖z - v‖ * q) * t := by
  have hre (x y : ℂ) : |x.re - y.re| ≤ ‖x - y‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (x - y)
  have hid := inner_difference z v H K hHK hK
  have hid' : |inner ℝ z H - inner ℝ v K| ≤ (r * e + ‖z - v‖ * q) * t := by
    exact hid.trans (mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hz he) le_rfl) ht)
  have hd : incD a b z H - incD a b v K =
      b * (z.re - v.re) + a * (H.re - K.re) + (inner ℝ z H - inner ℝ v K) := by
    unfold incD; ring
  rw [hd]
  calc
    _ ≤ |b * (z.re - v.re)| + |a * (H.re - K.re)| +
        |inner ℝ z H - inner ℝ v K| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (L * t) * ‖z - v‖ + M * (e * t) + (r * e + ‖z - v‖ * q) * t := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul hb (hre z v) (abs_nonneg _) (by positivity))
        (mul_le_mul ha ((hre H K).trans hHK) (abs_nonneg _) hM)) hid'
    _ = _ := by ring

private theorem scalar_gradient_difference (a b : ℝ) (z v H K : ℂ)
    {M L r e q t : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (he : 0 ≤ e) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (ha : |a| ≤ M) (hb : |b| ≤ L * t) (hz : ‖z‖ ≤ r) (hv : ‖v‖ ≤ r)
    (hHK : ‖H - K‖ ≤ e * t) (hK : ‖K‖ ≤ q * t) :
    |grad a b z H - grad a b v K| ≤
      (4 * L * (3 * M + 2 * r) * (‖z‖ + ‖v‖) * ‖z - v‖ +
        4 * (M ^ 2 + (2 * M + r) * (M + r)) * ‖z‖ * e +
        4 * (M ^ 2 + (2 * M + r) * r + (2 * M + 2 * r) * (M + r)) * q * ‖z - v‖) * t := by
  have h1 : |4 * a * b * (‖z‖ ^ 2 - ‖v‖ ^ 2)| ≤
      4 * M * (L * t) * ((‖z‖ + ‖v‖) * ‖z - v‖) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul (mul_le_mul
      (mul_le_mul_of_nonneg_left ha (by norm_num)) hb (abs_nonneg _) (by positivity))
      (sqdiff z v) (abs_nonneg _) (by positivity)
  have h2 : |4 * a ^ 2 * (inner ℝ z H - inner ℝ v K)| ≤
      4 * M ^ 2 * ((‖z‖ * e + ‖z - v‖ * q) * t) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_pow]
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg a) ha 2) (by norm_num))
      (inner_difference z v H K hHK hK) (abs_nonneg _) (by positivity)
  have hprod : |inc a z * incD a b z H - inc a v * incD a b v K| ≤
      (2 * M + r) * ‖z‖ * ((L * ‖z - v‖ + (M + r) * e + ‖z - v‖ * q) * t) +
        ((2 * M + 2 * r) * ‖z - v‖) * ((L * ‖v‖ + (M + r) * q) * t) := by
    rw [show inc a z * incD a b z H - inc a v * incD a b v K =
      inc a z * (incD a b z H - incD a b v K) +
        (inc a z - inc a v) * incD a b v K by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (inc_bound a z hM ha hz)
        (incD_difference a b z v H K hM hL he ht ha hb hz hHK hK) (abs_nonneg _) (by positivity))
      (mul_le_mul (inc_difference a z v hM ha hz hv)
        (incD_bound a b v K hM hL hq ht ha hb hv hK) (abs_nonneg _) (by positivity))
  have hsplit : grad a b z H - grad a b v K =
      4 * a * b * (‖z‖ ^ 2 - ‖v‖ ^ 2) +
      4 * a ^ 2 * (inner ℝ z H - inner ℝ v K) +
      4 * (inc a z * incD a b z H - inc a v * incD a b v K) := by
    unfold grad; ring
  rw [hsplit]
  calc
    _ ≤ |4 * a * b * (‖z‖ ^ 2 - ‖v‖ ^ 2)| +
        |4 * a ^ 2 * (inner ℝ z H - inner ℝ v K)| +
        |4 * (inc a z * incD a b z H - inc a v * incD a b v K)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * M * (L * t) * ((‖z‖ + ‖v‖) * ‖z - v‖) +
        4 * M ^ 2 * ((‖z‖ * e + ‖z - v‖ * q) * t) +
        4 * ((2 * M + r) * ‖z‖ * ((L * ‖z - v‖ + (M + r) * e + ‖z - v‖ * q) * t) +
          ((2 * M + 2 * r) * ‖z - v‖) * ((L * ‖v‖ + (M + r) * q) * t)) := by
      apply add_le_add (add_le_add h1 h2)
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      exact mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (4 * L * (3 * M + r) * ‖z‖ * ‖z - v‖ +
        4 * L * (3 * M + 2 * r) * ‖v‖ * ‖z - v‖ +
        4 * (M ^ 2 + (2 * M + r) * (M + r)) * ‖z‖ * e +
        4 * (M ^ 2 + (2 * M + 2 * r) * (M + r)) * q * ‖z - v‖ +
        4 * (2 * M + r) * ‖z‖ * q * ‖z - v‖) * t := by ring
    _ ≤ (4 * L * (3 * M + 2 * r) * ‖z‖ * ‖z - v‖ +
        4 * L * (3 * M + 2 * r) * ‖v‖ * ‖z - v‖ +
        4 * (M ^ 2 + (2 * M + r) * (M + r)) * ‖z‖ * e +
        4 * (M ^ 2 + (2 * M + 2 * r) * (M + r)) * q * ‖z - v‖ +
        4 * (2 * M + r) * r * q * ‖z - v‖) * t := by
      gcongr; linarith
    _ = _ := by ring

/-- Pointwise operator-norm difference, preserving integrable product factors. -/
theorem densityRemainder_gradient_difference_pointwise
    (w : Space → ℝ) (h k : Space → ℂ) {x : Space}
    (hw : DifferentiableAt ℝ w x) (hh : DifferentiableAt ℝ h x) (hk : DifferentiableAt ℝ k x)
    {M L r : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hwb : |w x| ≤ M) (hDwb : ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ‖h x‖ ≤ r) (hkb : ‖k x‖ ≤ r) :
    ‖fderiv ℝ (densityRemainder w h) x - fderiv ℝ (densityRemainder w k) x‖ ≤
      4 * L * (3 * M + 2 * r) * (‖h x‖ + ‖k x‖) * ‖h x - k x‖ +
      4 * (M ^ 2 + (2 * M + r) * (M + r)) * ‖h x‖ * ‖fderiv ℝ h x - fderiv ℝ k x‖ +
      4 * (M ^ 2 + (2 * M + r) * r + (2 * M + 2 * r) * (M + r)) * ‖fderiv ℝ k x‖ * ‖h x - k x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖fderiv ℝ (densityRemainder w h) x v - fderiv ℝ (densityRemainder w k) x v‖ ≤ _
  rw [densityRemainder_fderiv_apply w h hw hh v, densityRemainder_fderiv_apply w k hw hk v,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  change |grad (w x) (fderiv ℝ w x v) (h x) (fderiv ℝ h x v) -
    grad (w x) (fderiv ℝ w x v) (k x) (fderiv ℝ k x v)| ≤ _
  apply scalar_gradient_difference (w x) (fderiv ℝ w x v) (h x) (k x)
    (fderiv ℝ h x v) (fderiv ℝ k x v) hM hL hr
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hwb
  · have hb := (fderiv ℝ w x).le_opNorm v
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hDwb (norm_nonneg v))
  · exact hhb
  · exact hkb
  · exact (fderiv ℝ h x - fderiv ℝ k x).le_opNorm v
  · exact (fderiv ℝ k x).le_opNorm v

private theorem product_mass {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : Space → E) (g : Space → F) (hf : MemLp f 2) (hg : MemLp g 2)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfa : (∫ x : Space, ‖f x‖ ^ 2) ≤ a ^ 2)
    (hgb : (∫ x : Space, ‖g x‖ ^ 2) ≤ b ^ 2) :
    Integrable (fun x : Space => ‖f x‖ * ‖g x‖) ∧
      (∫ x : Space, ‖f x‖ * ‖g x‖) ≤ 2 * a * b := by
  have hp (x : Space) : ‖f x‖ * ‖g x‖ ≤
      (b / a) * ‖f x‖ ^ 2 + (a / b) * ‖g x‖ ^ 2 := by
    have he : (b / a) * ‖f x‖ ^ 2 + (a / b) * ‖g x‖ ^ 2 =
        (b ^ 2 * ‖f x‖ ^ 2 + a ^ 2 * ‖g x‖ ^ 2) / (a * b) := by field_simp
    rw [he]
    apply (le_div_iff₀ (mul_pos ha hb)).2
    nlinarith only [sq_nonneg (b * ‖f x‖ - a * ‖g x‖),
      mul_nonneg (mul_nonneg ha.le hb.le) (mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))]
  have hd := (hf.norm.integrable_sq.const_mul (b / a)).add (hg.norm.integrable_sq.const_mul (a / b))
  have hi : Integrable (fun x : Space => ‖f x‖ * ‖g x‖) := by
    apply hd.mono' (hf.aestronglyMeasurable.norm.mul hg.aestronglyMeasurable.norm)
    filter_upwards with x
    simpa only [Pi.add_apply, Pi.mul_apply,
      Real.norm_of_nonneg (mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))] using hp x
  refine ⟨hi, ?_⟩
  have hI := integral_mono_ae hi hd (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at hI
  rw [integral_add (hf.norm.integrable_sq.const_mul (b / a))
    (hg.norm.integrable_sq.const_mul (a / b)), integral_const_mul, integral_const_mul] at hI
  calc
    _ ≤ (b / a) * (∫ x : Space, ‖f x‖ ^ 2) + (a / b) * (∫ x : Space, ‖g x‖ ^ 2) := hI
    _ ≤ (b / a) * a ^ 2 + (a / b) * b ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hfa (by positivity))
        (mul_le_mul_of_nonneg_left hgb (by positivity))
    _ = _ := by field_simp; ring

/-- The real density-gradient difference is L1 with an O(r*d) mass and supremum. -/
theorem densityRemainder_gradient_difference_source
    (w : Space → ℝ) (h k : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    (hh2 : MemLp h 2) (hk2 : MemLp k 2)
    (hDh2 : MemLp (fderiv ℝ h) 2) (hDk2 : MemLp (fderiv ℝ k) 2)
    {M L r d : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 < r) (hd : 0 < d)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ∀ᵐ x, ‖h x‖ ≤ r) (hkb : ∀ᵐ x, ‖k x‖ ≤ r)
    (hDhb : ∀ᵐ x, ‖fderiv ℝ h x‖ ≤ r) (hDkb : ∀ᵐ x, ‖fderiv ℝ k x‖ ≤ r)
    (hdb : ∀ᵐ x, ‖h x - k x‖ ≤ d)
    (hDdb : ∀ᵐ x, ‖fderiv ℝ h x - fderiv ℝ k x‖ ≤ d)
    (hEh : (∫ x : Space, ‖h x‖ ^ 2) ≤ r ^ 2)
    (hEk : (∫ x : Space, ‖k x‖ ^ 2) ≤ r ^ 2)
    (hEDh : (∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) ≤ r ^ 2)
    (hEDk : (∫ x : Space, ‖fderiv ℝ k x‖ ^ 2) ≤ r ^ 2)
    (hEd : (∫ x : Space, ‖h x - k x‖ ^ 2) ≤ d ^ 2)
    (hEDd : (∫ x : Space, ‖fderiv ℝ h x - fderiv ℝ k x‖ ^ 2) ≤ d ^ 2) :
    let G := fun x => fderiv ℝ (densityRemainder w h) x - fderiv ℝ (densityRemainder w k) x
    Integrable G ∧ (∫ x : Space, ‖G x‖) ≤ 2 * densityGradientDifferenceConstant M L r * r * d ∧
      (∀ᵐ x, ‖G x‖ ≤ densityGradientDifferenceConstant M L r * r * d) := by
  dsimp only
  let A := 4 * L * (3 * M + 2 * r)
  let B := 4 * (M ^ 2 + (2 * M + r) * (M + r))
  let C := 4 * (M ^ 2 + (2 * M + r) * r + (2 * M + 2 * r) * (M + r))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hconst : densityGradientDifferenceConstant M L r = 2 * A + B + C := by
    unfold densityGradientDifferenceConstant; dsimp [A, B, C]; ring
  have ih := (densityRemainder_gradient_quadratic w h hw hh hh2 hDh2 hM hL hr.le
    hwb hDwb hhb hDhb hEh hEDh).1
  have ik := (densityRemainder_gradient_quadratic w k hw hk hk2 hDk2 hM hL hr.le
    hwb hDwb hkb hDkb hEk hEDk).1
  have hb : ∀ᵐ x,
      ‖fderiv ℝ (densityRemainder w h) x - fderiv ℝ (densityRemainder w k) x‖ ≤
        A * (‖h x‖ + ‖k x‖) * ‖h x - k x‖ +
        B * ‖h x‖ * ‖fderiv ℝ h x - fderiv ℝ k x‖ + C * ‖fderiv ℝ k x‖ * ‖h x - k x‖ := by
    filter_upwards [hwb, hDwb, hhb, hkb] with x hx hdx hhx hkx
    exact densityRemainder_gradient_difference_pointwise w h k
      (hw.differentiable (by norm_num) x) (hh.differentiable (by norm_num) x)
      (hk.differentiable (by norm_num) x) hM hL hr.le hx hdx hhx hkx
  have p1 := product_mass h (fun x => h x - k x) hh2 (hh2.sub hk2) hr hd hEh hEd
  have p2 := product_mass k (fun x => h x - k x) hk2 (hh2.sub hk2) hr hd hEk hEd
  have p3 := product_mass h (fun x => fderiv ℝ h x - fderiv ℝ k x)
    hh2 (hDh2.sub hDk2) hr hd hEh hEDd
  have p4 := product_mass (fderiv ℝ k) (fun x => h x - k x)
    hDk2 (hh2.sub hk2) hr hd hEDk hEd
  have hmajor := (((p1.1.add p2.1).const_mul A).add (p3.1.const_mul B)).add (p4.1.const_mul C)
  refine ⟨ih.sub ik, ?_, ?_⟩
  · have hI := integral_mono_ae (ih.sub ik).norm hmajor (hb.mono fun x hx => by
      change ‖fderiv ℝ (densityRemainder w h) x - fderiv ℝ (densityRemainder w k) x‖ ≤
        (A * (‖h x‖ * ‖h x - k x‖ + ‖k x‖ * ‖h x - k x‖) +
          B * (‖h x‖ * ‖fderiv ℝ h x - fderiv ℝ k x‖)) +
          C * (‖fderiv ℝ k x‖ * ‖h x - k x‖)
      exact hx.trans_eq (by ring))
    have hi12 := integral_add p1.1 p2.1
    have hiAB := integral_add ((p1.1.add p2.1).const_mul A) (p3.1.const_mul B)
    have hiABC := integral_add (((p1.1.add p2.1).const_mul A).add (p3.1.const_mul B)) (p4.1.const_mul C)
    simp only [Pi.add_apply, Pi.sub_apply] at hI hi12 hiAB hiABC
    rw [hiABC, hiAB, integral_const_mul, integral_const_mul, integral_const_mul, hi12] at hI
    calc
      _ ≤ A * ((∫ x : Space, ‖h x‖ * ‖h x - k x‖) + ∫ x : Space, ‖k x‖ * ‖h x - k x‖) +
          B * (∫ x : Space, ‖h x‖ * ‖fderiv ℝ h x - fderiv ℝ k x‖) +
          C * (∫ x : Space, ‖fderiv ℝ k x‖ * ‖h x - k x‖) := hI
      _ ≤ A * (2 * r * d + 2 * r * d) + B * (2 * r * d) + C * (2 * r * d) := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add p1.2 p2.2) hA)
          (mul_le_mul_of_nonneg_left p3.2 hB)) (mul_le_mul_of_nonneg_left p4.2 hC)
      _ = _ := by rw [hconst]; ring
  · filter_upwards [hb, hhb, hkb, hDkb, hdb, hDdb] with x hx hhx hkx hdkx hdx hddx
    apply hx.trans
    calc
      _ ≤ A * (r + r) * d + B * r * d + C * r * d := by gcongr
      _ = _ := by rw [hconst]; ring

/-- Actual density-potential difference and its actual spatial derivative both
have the contraction-scale r*d factor. All convolution integrability is derived. -/
theorem densityRemainder_potential_first_order_difference
    (w : Space → ℝ) (h k : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    (hh2 : MemLp h 2) (hk2 : MemLp k 2)
    (hDh2 : MemLp (fderiv ℝ h) 2) (hDk2 : MemLp (fderiv ℝ k) 2)
    {M L r d : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hr : 0 < r) (hd : 0 < d)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hhb : ∀ᵐ x, ‖h x‖ ≤ r) (hkb : ∀ᵐ x, ‖k x‖ ≤ r)
    (hDhb : ∀ᵐ x, ‖fderiv ℝ h x‖ ≤ r) (hDkb : ∀ᵐ x, ‖fderiv ℝ k x‖ ≤ r)
    (hdb : ∀ᵐ x, ‖h x - k x‖ ≤ d)
    (hDdb : ∀ᵐ x, ‖fderiv ℝ h x - fderiv ℝ k x‖ ≤ d)
    (hEh : (∫ x : Space, ‖h x‖ ^ 2) ≤ r ^ 2)
    (hEk : (∫ x : Space, ‖k x‖ ^ 2) ≤ r ^ 2)
    (hEDh : (∫ x : Space, ‖fderiv ℝ h x‖ ^ 2) ≤ r ^ 2)
    (hEDk : (∫ x : Space, ‖fderiv ℝ k x‖ ^ 2) ≤ r ^ 2)
    (hEd : (∫ x : Space, ‖h x - k x‖ ^ 2) ≤ d ^ 2)
    (hEDd : (∫ x : Space, ‖fderiv ℝ h x - fderiv ℝ k x‖ ^ 2) ≤ d ^ 2) (x : Space) :
    HasFDerivAt (fun y => potential (densityRemainder w h) y - potential (densityRemainder w k) y)
      (gradientPotential (fderiv ℝ (densityRemainder w h)) x -
        gradientPotential (fderiv ℝ (densityRemainder w k)) x) x ∧
    ‖potential (densityRemainder w h) x - potential (densityRemainder w k) x‖ ≤
      densityPotentialDifferenceConstant M r * r * d ∧
    ‖fderiv ℝ (potential (densityRemainder w h)) x -
        fderiv ℝ (potential (densityRemainder w k)) x‖ ≤
      (nearMass + 2) * densityGradientDifferenceConstant M L r * r * d := by
  have sh := densityRemainder_gradient_quadratic w h hw hh hh2 hDh2 hM hL hr.le
    hwb hDwb hhb hDhb hEh hEDh
  have sk := densityRemainder_gradient_quadratic w k hw hk hk2 hDk2 hM hL hr.le
    hwb hDwb hkb hDkb hEk hEDk
  have sd := densityRemainder_gradient_difference_source w h k hw hh hk hh2 hk2 hDh2 hDk2
    hM hL hr hd hwb hDwb hhb hkb hDhb hDkb hdb hDdb hEh hEk hEDh hEDk hEd hEDd
  have ph := densityRemainder_potential_gradient_quadratic w h hw hh hh2 hDh2 hM hL hr.le
    hwb hDwb hhb hDhb hEh hEDh x
  have pk := densityRemainder_potential_gradient_quadratic w k hw hk hk2 hDk2 hM hL hr.le
    hwb hDwb hkb hDkb hEk hEDk x
  have hC : 0 ≤ densityGradientQuadraticConstant M L r := by
    unfold densityGradientQuadraticConstant; positivity
  have hD : 0 ≤ densityGradientDifferenceConstant M L r := by
    unfold densityGradientDifferenceConstant; positivity
  refine ⟨ph.1.sub pk.1, densityRemainder_potential_difference w h k
    hw.continuous.aestronglyMeasurable hh2 hk2 hM hr hd hwb hhb hkb hdb hEh hEk hEd x, ?_⟩
  rw [ph.1.fderiv, pk.1.fderiv]
  have hg := gradientPotential_difference_bound
    (fderiv ℝ (densityRemainder w h)) (fderiv ℝ (densityRemainder w k)) sh.1 sk.1
    (densityGradientQuadraticConstant M L r * r ^ 2)
    (densityGradientQuadraticConstant M L r * r ^ 2)
    (densityGradientDifferenceConstant M L r * r * d)
    (by positivity) (by positivity) (by positivity) sh.2.2 sk.2.2 sd.2.2 x
  exact (hg.trans (add_le_add le_rfl sd.2.1)).trans_eq (by ring)

end HBL.RegularRadiation.PhysicalExpansion
