import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledCancellation
import Mathlib.Tactic

/-!
# Explicit real Cramer selector for the coupled Hartree compatibility system

The strict nondegeneracy proof already used the two-by-two real Cramer
formula internally, but the selected pair was returned only existentially.
This file exposes the SAME formula as a definition.  Downstream time
differentiation can therefore act on a concrete function rather than an
existential witness.

No new invertibility assumption is introduced: cancellation and uniqueness
require exactly the same nonzero real determinant as the accepted coupled
matrix theorem.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

def actualRealCramerCorrection (b w Z : ℂ) : ℝ × ℝ :=
  let d := b.re * w.im - w.re * b.im
  ((w.re * Z.im - w.im * Z.re) / d,
   (b.im * Z.re - b.re * Z.im) / d)

theorem actual_real_Cramer_correction_cancel
    (b w Z : ℂ)
    (hdet : b.re * w.im - w.re * b.im ≠ 0) :
    let p := actualRealCramerCorrection b w Z
    Z + (p.1 : ℂ) * b + (p.2 : ℂ) * w = 0 := by
  dsimp only
  let d : ℝ := b.re * w.im - w.re * b.im
  have hd : d ≠ 0 := hdet
  let p : ℝ × ℝ := actualRealCramerCorrection b w Z
  have hp1 :
      p.1 * d = w.re * Z.im - w.im * Z.re := by
    dsimp [p, actualRealCramerCorrection, d]
    exact div_mul_cancel₀ _ hd
  have hp2 :
      p.2 * d = b.im * Z.re - b.re * Z.im := by
    dsimp [p, actualRealCramerCorrection, d]
    exact div_mul_cancel₀ _ hd
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero]
    have hprod :
        (Z.re + p.1 * b.re + p.2 * w.re) * d = 0 := by
      calc
        _ = Z.re * d + (p.1 * d) * b.re + (p.2 * d) * w.re := by ring
        _ = 0 := by
          rw [hp1, hp2]
          dsimp [d]
          ring
    exact (mul_eq_zero.mp hprod).resolve_right hd
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_im, zero_mul, add_zero]
    have hprod :
        (Z.im + p.1 * b.im + p.2 * w.im) * d = 0 := by
      calc
        _ = Z.im * d + (p.1 * d) * b.im + (p.2 * d) * w.im := by ring
        _ = 0 := by
          rw [hp1, hp2]
          dsimp [d]
          ring
    exact (mul_eq_zero.mp hprod).resolve_right hd

theorem actual_real_Cramer_correction_unique
    (b w Z : ℂ)
    (hdet : b.re * w.im - w.re * b.im ≠ 0) :
    let p := actualRealCramerCorrection b w Z
    (Z + (p.1 : ℂ) * b + (p.2 : ℂ) * w = 0) ∧
    ∀ q : ℝ × ℝ,
      Z + (q.1 : ℂ) * b + (q.2 : ℂ) * w = 0 → q = p := by
  dsimp only
  let d : ℝ := b.re * w.im - w.re * b.im
  let p : ℝ × ℝ := actualRealCramerCorrection b w Z
  have hd : d ≠ 0 := hdet
  have hp := actual_real_Cramer_correction_cancel b w Z hdet
  refine ⟨by simpa only [p] using hp, ?_⟩
  intro q hq
  have hr := congrArg Complex.re hq
  have hi := congrArg Complex.im hq
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero] at hr
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_im, zero_mul, add_zero] at hi
  apply Prod.ext
  · change q.1 =
      (w.re * Z.im - w.im * Z.re) / d
    apply (eq_div_iff hd).2
    dsimp [d]
    linear_combination w.im * hr - w.re * hi
  · change q.2 =
      (b.im * Z.re - b.re * Z.im) / d
    apply (eq_div_iff hd).2
    dsimp [d]
    linear_combination b.re * hi - b.im * hr

def actualMomentLockedCramerCorrection
    {mu theta scale : ℝ} (K : HBL.Profile.Kummer.OriginKummerPair mu theta scale)
    (L c : ℝ) (hL : 0 < L) (a r0 r1 : ℝ) (Z : ℂ) : ℝ × ℝ :=
  let cols := actualMomentLockedCoupledColumns K L c hL a r0 r1
  actualRealCramerCorrection cols.1 cols.2 Z

theorem actual_Hartree_moment_locked_Cramer_correction_unique
    {mu theta scale : ℝ}
    (K : HBL.Profile.Kummer.OriginKummerPair mu theta scale)
    (L c : ℝ) (hL : 0 < L) (a r0 r1 : ℝ) (Z : ℂ)
    (hdet : actualMomentLockedCoupledDeterminant
      K L c hL a r0 r1 ≠ 0) :
    let cols := actualMomentLockedCoupledColumns K L c hL a r0 r1
    let p := actualMomentLockedCramerCorrection K L c hL a r0 r1 Z
    (Z + (p.1 : ℂ) * cols.1 + (p.2 : ℂ) * cols.2 = 0) ∧
    ∀ q : ℝ × ℝ,
      Z + (q.1 : ℂ) * cols.1 + (q.2 : ℂ) * cols.2 = 0 → q = p := by
  dsimp only
  let cols := actualMomentLockedCoupledColumns K L c hL a r0 r1
  have hdet' : cols.1.re * cols.2.im - cols.2.re * cols.1.im ≠ 0 := by
    simpa only [actualMomentLockedCoupledDeterminant, cols] using hdet
  simpa only [actualMomentLockedCramerCorrection, cols] using
    actual_real_Cramer_correction_unique cols.1 cols.2 Z hdet'

end HBL.TypeIIDynamicSelection
