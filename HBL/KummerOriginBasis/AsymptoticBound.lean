import HBL.KummerOriginBasis.UniformBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- Quantitative singular/regular value asymptotics, obtained from the actual ODE. -/
theorem origin_kummer_asymptotic_bound {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G) :
    ∀ r ∈ Ioc 0 R,
      ‖originPhysicalValue K.y r - (r : ℂ)⁻¹‖ ≤ D * G * r ∧
      ‖originPhysicalValue K.x r - 1‖ ≤ (D + 1) * G * r ^ 2 := by
  have move (f g : ℝ → ℂ)
      (hf : ∀ t ∈ Icc 0 R, HasDerivWithinAt f (g t) (Icc 0 R) t)
      (r : ℝ) (hr : r ∈ Icc 0 R) (C : ℝ)
      (hg : ∀ t ∈ Ico 0 r, ‖g t‖ ≤ C) : ‖f r - f 0‖ ≤ C * r := by
    have hs : Icc 0 r ⊆ Icc 0 R := Icc_subset_Icc_right hr.2
    simpa only [sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hf t (hs ht)).mono hs) hg r ⟨hr.1, le_rfl⟩
  have hdy (r : ℝ) (hr : r ∈ Icc 0 R) : ‖K.dy r‖ ≤ D * G * r := by
    have h := move K.dy _ K.dy_deriv r hr (D * G) (by
      intro t ht
      have htR : t ∈ Icc 0 R := ⟨ht.1, ht.2.le.trans hr.2⟩
      have hB := hbound t htR
      calc
        _ ≤ ‖originFirstCoeff t‖ * ‖K.dy t‖ + ‖originZeroCoeff mu theta‖ * ‖K.y t‖ := by
          simpa only [norm_neg, norm_mul] using norm_add_le
            (originFirstCoeff t * K.dy t) (originZeroCoeff mu theta * K.y t)
        _ ≤ ‖originFirstCoeff t‖ * G + ‖originZeroCoeff mu theta‖ * G := by gcongr; exact hB.2.1; exact hB.1
        _ = (‖originFirstCoeff t‖ + ‖originZeroCoeff mu theta‖) * G := by ring
        _ ≤ D * G := mul_le_mul_of_nonneg_right (hcoeff t htR) hG)
    simpa only [K.dy_zero, sub_zero] using h
  have hy (r : ℝ) (hr : r ∈ Icc 0 R) : ‖K.y r - 1‖ ≤ D * G * r ^ 2 := by
    have h := move K.y K.dy K.y_deriv r hr (D * G * r) (by
      intro t ht
      exact (hdy t ⟨ht.1, ht.2.le.trans hr.2⟩).trans
        (mul_le_mul_of_nonneg_left ht.2.le (mul_nonneg hD hG)))
    simpa only [K.y_zero, pow_two, mul_assoc] using h
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
        _ ≤ ‖originFirstCoeff t‖ * ‖K.dx t‖ + ‖originZeroCoeff mu theta‖ * ‖K.x t‖ := by
          simpa only [norm_neg, norm_mul] using norm_add_le
            (originFirstCoeff t * K.dx t) (originZeroCoeff mu theta * K.x t)
        _ ≤ (t / 2) * G + D * (G * t) := by
          rw [ha]
          exact add_le_add (mul_le_mul_of_nonneg_left hB.2.2.2 (div_nonneg ht.1 (by norm_num)))
            (mul_le_mul hb (hx t htR) (norm_nonneg _) hD)
        _ ≤ (D + 1) * G * t := by nlinarith [mul_nonneg hG ht.1]
        _ ≤ (D + 1) * G * r := mul_le_mul_of_nonneg_left ht.2.le (by positivity))
    simpa only [K.dx_zero, pow_two, mul_assoc] using h
  have hxr (r : ℝ) (hr : r ∈ Icc 0 R) :
      ‖K.x r - (r : ℂ)‖ ≤ (D + 1) * G * r ^ 3 := by
    have hf : ∀ t ∈ Icc 0 R, HasDerivWithinAt (fun s : ℝ => K.x s - (s : ℂ))
        (K.dx t - 1) (Icc 0 R) t := by
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
  intro r hr
  have hr' : r ∈ Icc 0 R := ⟨hr.1.le, hr.2⟩
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.1.ne'
  constructor
  · have heq : originPhysicalValue K.y r - (r : ℂ)⁻¹ = (K.y r - 1) / (r : ℂ) := by
      dsimp [originPhysicalValue]
      rw [sub_div, one_div]
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    apply (div_le_iff₀ hr.1).2
    simpa only [pow_two, mul_assoc] using hy r hr'
  · have heq : originPhysicalValue K.x r - 1 = (K.x r - (r : ℂ)) / (r : ℂ) := by
      dsimp [originPhysicalValue]
      rw [sub_div, div_self hn]
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    apply (div_le_iff₀ hr.1).2
    simpa only [pow_succ, mul_assoc] using hxr r hr'
end HBL.Profile.Kummer
