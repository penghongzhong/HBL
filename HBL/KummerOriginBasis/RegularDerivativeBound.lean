import HBL.KummerOriginBasis.AsymptoticBound
import Mathlib.Tactic

/-!
Quantitative regular value AND slope bounds for the actual origin-normalized
Kummer pair.  The two jet estimates are extracted from the same ODE argument
as `origin_kummer_asymptotic_bound`; no independently prescribed boundary
jets are introduced.  `origin_kummer_pair_bound` supplies the input G from
the coefficient bound D, uniformly on a fixed compact parameter set.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set

namespace HBL.Profile.Kummer

/-- The actual regularized origin solution has a cubic value error and a
quadratic derivative error, with the same fixed coefficient/solution bound. -/
theorem origin_kummer_regular_jet_bound {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G) :
    ∀ r ∈ Icc 0 R,
      ‖K.x r - (r : ℂ)‖ ≤ (D + 1) * G * r ^ 3 ∧
      ‖K.dx r - 1‖ ≤ (D + 1) * G * r ^ 2 := by
  have move (f g : ℝ → ℂ)
      (hf : ∀ t ∈ Icc 0 R, HasDerivWithinAt f (g t) (Icc 0 R) t)
      (r : ℝ) (hr : r ∈ Icc 0 R) (C : ℝ)
      (hg : ∀ t ∈ Ico 0 r, ‖g t‖ ≤ C) : ‖f r - f 0‖ ≤ C * r := by
    have hs : Icc 0 r ⊆ Icc 0 R := Icc_subset_Icc_right hr.2
    simpa only [sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hf t (hs ht)).mono hs) hg r ⟨hr.1, le_rfl⟩
  have hx (r : ℝ) (hr : r ∈ Icc 0 R) : ‖K.x r‖ ≤ G * r := by
    have h := move K.x K.dx K.x_deriv r hr G
      (fun t ht => (hbound t ⟨ht.1, ht.2.le.trans hr.2⟩).2.2.2)
    simpa only [K.x_zero, sub_zero] using h
  have hdx (r : ℝ) (hr : r ∈ Icc 0 R) :
      ‖K.dx r - 1‖ ≤ (D + 1) * G * r ^ 2 := by
    have h := move K.dx _ K.dx_deriv r hr ((D + 1) * G * r) (by
      intro t ht
      have htR : t ∈ Icc 0 R := ⟨ht.1, ht.2.le.trans hr.2⟩
      have hB := hbound t htR
      have ha : ‖originFirstCoeff t‖ = t / 2 := by
        simp [originFirstCoeff, abs_of_nonneg ht.1]
      have hb : ‖originZeroCoeff mu theta‖ ≤ D := by
        have hc := hcoeff t htR
        linarith [norm_nonneg (originFirstCoeff t)]
      calc
        _ ≤ ‖originFirstCoeff t‖ * ‖K.dx t‖ +
            ‖originZeroCoeff mu theta‖ * ‖K.x t‖ := by
          simpa only [norm_neg, norm_mul] using norm_add_le
            (originFirstCoeff t * K.dx t) (originZeroCoeff mu theta * K.x t)
        _ ≤ (t / 2) * G + D * (G * t) := by
          rw [ha]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hB.2.2.2 (div_nonneg ht.1 (by norm_num)))
            (mul_le_mul hb (hx t htR) (norm_nonneg _) hD)
        _ ≤ (D + 1) * G * t := by nlinarith [mul_nonneg hG ht.1]
        _ ≤ (D + 1) * G * r :=
          mul_le_mul_of_nonneg_left ht.2.le (by positivity))
    simpa only [K.dx_zero, pow_two, mul_assoc] using h
  have hxr (r : ℝ) (hr : r ∈ Icc 0 R) :
      ‖K.x r - (r : ℂ)‖ ≤ (D + 1) * G * r ^ 3 := by
    have hf : ∀ t ∈ Icc 0 R, HasDerivWithinAt
        (fun s : ℝ => K.x s - (s : ℂ)) (K.dx t - 1) (Icc 0 R) t := by
      intro t ht
      have hc : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
        simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
          Complex.ofRealCLM.hasDerivAt (x := t)
      exact (K.x_deriv t ht).sub hc.hasDerivWithinAt
    have h := move _ _ hf r hr ((D + 1) * G * r ^ 2) (by
      intro t ht
      apply (hdx t ⟨ht.1, ht.2.le.trans hr.2⟩).trans
      gcongr <;> linarith [ht.1, ht.2])
    simpa only [Complex.ofReal_zero, K.x_zero, sub_zero, pow_succ, mul_assoc] using h
  exact fun r hr => ⟨hxr r hr, hdx r hr⟩

/-- The actual physical regular mode k=x/r has a bounded value and a slope
of order r. The constants do not deteriorate as the left endpoint tends to 0. -/
theorem origin_kummer_regular_physical_bound {mu theta R B : ℝ}
    (K : OriginKummerPair mu theta R) (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hBR : B ≤ R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G) :
    ∀ r ∈ Ioc 0 B,
      ‖originPhysicalValue K.x r‖ ≤ 1 + (D + 1) * G * B ^ 2 ∧
      ‖originPhysicalSlope K.x K.dx r‖ ≤ 2 * ((D + 1) * G) * r := by
  intro r hr
  have hrR : r ∈ Icc 0 R := ⟨hr.1.le, hr.2.trans hBR⟩
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.1.ne'
  have hj := origin_kummer_regular_jet_bound K D G hD hG hcoeff hbound r hrR
  have hv := (origin_kummer_asymptotic_bound K D G hD hG hcoeff hbound
    r ⟨hr.1, hrR.2⟩).2
  constructor
  · have ht := norm_add_le (originPhysicalValue K.x r - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    calc
      _ ≤ ‖originPhysicalValue K.x r - 1‖ + 1 := ht
      _ ≤ (D + 1) * G * r ^ 2 + 1 := by linarith only [hv]
      _ ≤ 1 + (D + 1) * G * B ^ 2 := by
        have hsq : r ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hr.1.le hr.2 2
        have hh := mul_le_mul_of_nonneg_left hsq
          (show 0 ≤ (D + 1) * G by positivity)
        linarith
  · have heq : originPhysicalSlope K.x K.dx r =
        (K.dx r - 1) / (r : ℂ) - (K.x r - (r : ℂ)) / (r : ℂ) ^ 2 := by
      unfold originPhysicalSlope
      field_simp [hrC] <;> ring
    rw [heq]
    calc
      _ ≤ ‖(K.dx r - 1) / (r : ℂ)‖ +
          ‖(K.x r - (r : ℂ)) / (r : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = ‖K.dx r - 1‖ / r + ‖K.x r - (r : ℂ)‖ / r ^ 2 := by
        simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr.1]
      _ ≤ ((D + 1) * G * r ^ 2) / r +
          ((D + 1) * G * r ^ 3) / r ^ 2 :=
        add_le_add (div_le_div_of_nonneg_right hj.2 hr.1.le)
          (div_le_div_of_nonneg_right hj.1 (sq_nonneg r))
      _ = 2 * ((D + 1) * G) * r := by
        field_simp [hr.1.ne'] <;> ring

end HBL.Profile.Kummer
