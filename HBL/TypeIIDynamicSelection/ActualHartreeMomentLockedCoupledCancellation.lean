import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedConstructedNondegeneracy

/-!
The actual nondegenerate full columns determine a unique pair of REAL
speed increments cancelling any complex frozen compatibility residual.
The finite-dimensional solve is constructed by Cramer's formula. No
independently chosen inner trace, free affine charge, or assumed solution
is used. This is the frozen compatibility solve; moving-configuration and
full PDE residual estimates remain separate obligations.
-/

noncomputable section
set_option autoImplicit false
open Set

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

private theorem complex_columns_unique_real_cancellation (b w Z : ℂ)
    (hdet : b.re * w.im - w.re * b.im ≠ 0) :
    ∃! p : ℝ × ℝ, Z + (p.1 : ℂ) * b + (p.2 : ℂ) * w = 0 := by
  let d : ℝ := b.re * w.im - w.re * b.im
  let p : ℝ × ℝ :=
    ((w.re * Z.im - w.im * Z.re) / d,
     (b.im * Z.re - b.re * Z.im) / d)
  have hd : d ≠ 0 := hdet
  refine ⟨p, ?_, ?_⟩
  · apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero]
      dsimp only [p, d]
      field_simp [hdet]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.zero_im, zero_mul, add_zero]
      dsimp only [p, d]
      field_simp [hdet]
      ring
  · intro q hq
    have hr := congrArg Complex.re hq
    have hi := congrArg Complex.im hq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero] at hr
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_im, zero_mul, add_zero] at hi
    apply Prod.ext
    · change q.1 = (w.re * Z.im - w.im * Z.re) / d
      apply (eq_div_iff hd).2
      dsimp only [d]
      linear_combination w.im * hr - w.re * hi
    · change q.2 = (b.im * Z.re - b.re * Z.im) / d
      apply (eq_div_iff hd).2
      dsimp only [d]
      linear_combination b.re * hi - b.im * hr

/-- The same explicit physical region that makes the actual coupled matrix
nondegenerate admits a unique real scale/phase correction for every complex
compatibility residual. The determinant is proved inside this theorem. -/
theorem actual_Hartree_moment_locked_coupled_unique_cancellation_region
    {mu theta R B : ℝ} (K : OriginKummerPair mu theta R)
    (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B) (hBR : B < R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon : ℝ, 3 ≤ L0 ∧ 0 < epsilon ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → |c| ≤ 1 → a * |c| ≤ epsilon →
        let cols := actualMomentLockedCoupledColumns K L c hLp a (L / a) B
        ∀ Z : ℂ, ∃! p : ℝ × ℝ,
          Z + (p.1 : ℂ) * cols.1 + (p.2 : ℂ) * cols.2 = 0 := by
  obtain ⟨L0, epsilon, hL0, hepsilon, hRegion⟩ :=
    actual_Hartree_moment_locked_coupled_nondegenerate_region
      K D G hD hG hB hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, hL0, hepsilon, ?_⟩
  intro L c a hLp hLarge ha hc hSmall
  dsimp only
  intro Z
  let cols := actualMomentLockedCoupledColumns K L c hLp a (L / a) B
  have hPositive : 0 < cols.1.re * cols.2.im - cols.2.re * cols.1.im :=
    (hRegion L c a hLp hLarge ha hc hSmall).2
  exact complex_columns_unique_real_cancellation cols.1 cols.2 Z hPositive.ne'

/-- Construct the original Kummer basis and its actual nondegenerate
parameter region, then solve every frozen complex compatibility residual
by a unique real scale/phase increment. No basis or bound is supplied. -/
theorem actual_Hartree_moment_locked_constructed_unique_cancellation
    (mu theta : ℝ) :
    ∃ (K : OriginKummerPair mu theta 1) (B L0 epsilon : ℝ),
      0 < B ∧ B < 1 ∧ 3 ≤ L0 ∧ 0 < epsilon ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → |c| ≤ 1 → a * |c| ≤ epsilon →
        let cols := actualMomentLockedCoupledColumns K L c hLp a (L / a) B
        ∀ Z : ℂ, ∃! p : ℝ × ℝ,
          Z + (p.1 : ℂ) * cols.1 + (p.2 : ℂ) * cols.2 = 0 := by
  obtain ⟨K, B, L0, epsilon, hB, hBOne, hL0, hepsilon, hRegion⟩ :=
    actual_Hartree_moment_locked_constructed_nondegeneracy mu theta
  refine ⟨K, B, L0, epsilon, hB, hBOne, hL0, hepsilon, ?_⟩
  intro L c a hLp hLarge ha hc hSmall
  dsimp only
  intro Z
  let cols := actualMomentLockedCoupledColumns K L c hLp a (L / a) B
  have hPositive : 0 < cols.1.re * cols.2.im - cols.2.re * cols.1.im :=
    (hRegion L c a hLp hLarge ha hc hSmall).2
  exact complex_columns_unique_real_cancellation cols.1 cols.2 Z hPositive.ne'

end HBL.TypeIIDynamicSelection
