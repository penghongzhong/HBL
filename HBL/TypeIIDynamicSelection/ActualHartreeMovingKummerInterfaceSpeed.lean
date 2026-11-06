import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Exact motion of the physical Kummer lower interface

The physical lower interface is
  r0(s)=ell(s)^(-1/16)/a(s).
Under the actual modulation identity ell_s=-b ell, its logarithmic speed is
  r0_s/r0 = b/16 - a_s/a.

This is an exact chain-rule statement.  It does not prescribe the final
Type-II concentration law.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

def actualHartreeMovingKummerLowerInterface
    (ell a : ℝ → ℝ) (s : ℝ) : ℝ :=
  actualHartreeSlowInnerRadius (ell s) / a s

theorem actual_Hartree_slow_inner_radius_hasDerivAt
    (ell : ℝ → ℝ) (b s : ℝ)
    (hell : 0 < ell s)
    (hEll : HasDerivAt ell (-(b * ell s)) s) :
    HasDerivAt
      (fun t => actualHartreeSlowInnerRadius (ell t))
      ((b / 16) * actualHartreeSlowInnerRadius (ell s)) s := by
  let p : ℝ := -(1 / 16 : ℝ)
  have hpow0 :=
    Real.hasDerivAt_rpow_const (x := ell s) (p := p)
      (Or.inl hell.ne')
  have hcomp := hpow0.comp s hEll
  have hpow :
      (ell s) ^ (p - 1) * ell s = (ell s) ^ p := by
    calc
      (ell s) ^ (p - 1) * ell s =
          (ell s) ^ (p - 1) * (ell s) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (ell s) ^ ((p - 1) + 1) := by
            rw [← Real.rpow_add hell]
      _ = (ell s) ^ p := by congr 1 <;> ring
  have hcoef :
      (p * (ell s) ^ (p - 1)) * (-(b * ell s)) =
        (b / 16) * (ell s) ^ p := by
    rw [show (p * (ell s) ^ (p - 1)) * (-(b * ell s)) =
      (-p * b) * ((ell s) ^ (p - 1) * ell s) by ring]
    rw [hpow]
    dsimp [p]
    ring
  unfold actualHartreeSlowInnerRadius
  simpa only [p, hcoef, Function.comp_apply] using hcomp

theorem actual_Hartree_moving_Kummer_lower_interface_hasDerivAt
    (ell a : ℝ → ℝ) (b s adot : ℝ)
    (hell : 0 < ell s) (ha : 0 < a s)
    (hEll : HasDerivAt ell (-(b * ell s)) s)
    (hA : HasDerivAt a adot s) :
    let r0 := actualHartreeMovingKummerLowerInterface ell a
    HasDerivAt r0
      (r0 s * (b / 16 - adot / a s)) s := by
  dsimp only
  let L : ℝ → ℝ := fun t => actualHartreeSlowInnerRadius (ell t)
  have hL :
      HasDerivAt L ((b / 16) * L s) s := by
    dsimp [L]
    exact actual_Hartree_slow_inner_radius_hasDerivAt ell b s hell hEll
  have hdiv := hL.div hA ha.ne'
  have hEq :
      ((b / 16) * L s * a s - L s * adot) / (a s) ^ 2 =
        (L s / a s) * (b / 16 - adot / a s) := by
    field_simp [ha.ne']
  change HasDerivAt (fun t => L t / a t)
    ((L s / a s) * (b / 16 - adot / a s)) s
  rw [← hEq]
  exact hdiv

theorem actual_Hartree_moving_Kummer_lower_interface_speed_bound
    (ell a : ℝ → ℝ) (b s adot Cb Ca : ℝ)
    (hell : 0 < ell s) (ha : 0 < a s)
    (hs : 1 ≤ s) (_hCb : 0 ≤ Cb) (_hCa : 0 ≤ Ca)
    (hEll : HasDerivAt ell (-(b * ell s)) s)
    (hA : HasDerivAt a adot s)
    (hb : |b| ≤ Cb * s ^ (-1 : ℝ))
    (haRel : |adot| / a s ≤ Ca * s ^ (-1 : ℝ)) :
    let r0 := actualHartreeMovingKummerLowerInterface ell a
    ∃ r0dot : ℝ,
      HasDerivAt r0 r0dot s ∧
      |r0dot| ≤ r0 s * (Cb / 16 + Ca) * s ^ (-1 : ℝ) := by
  dsimp only
  let r0 := actualHartreeMovingKummerLowerInterface ell a
  let r0dot := r0 s * (b / 16 - adot / a s)
  have hDer :
      HasDerivAt r0 r0dot s := by
    dsimp [r0dot, r0]
    exact actual_Hartree_moving_Kummer_lower_interface_hasDerivAt
      ell a b s adot hell ha hEll hA
  have hr0pos : 0 < r0 s := by
    dsimp [r0, actualHartreeMovingKummerLowerInterface]
    exact div_pos (Real.rpow_pos_of_pos hell _) ha
  have hb16 : |b / 16| ≤ (Cb / 16) * s ^ (-1 : ℝ) := by
    calc
      |b / 16| = |b| / 16 := by
        rw [abs_div]
        norm_num
      _ ≤ (Cb * s ^ (-1 : ℝ)) / 16 :=
        div_le_div_of_nonneg_right hb (by norm_num)
      _ = (Cb / 16) * s ^ (-1 : ℝ) := by ring
  have hrelAbs :
      |adot / a s| = |adot| / a s := by
    rw [abs_div, abs_of_pos ha]
  have hsum :
      |b / 16 - adot / a s| ≤
        (Cb / 16 + Ca) * s ^ (-1 : ℝ) := by
    calc
      _ ≤ |b / 16| + |adot / a s| := abs_sub _ _
      _ = |b / 16| + |adot| / a s := by rw [hrelAbs]
      _ ≤ (Cb / 16) * s ^ (-1 : ℝ) +
          Ca * s ^ (-1 : ℝ) := add_le_add hb16 haRel
      _ = (Cb / 16 + Ca) * s ^ (-1 : ℝ) := by ring
  refine ⟨r0dot, hDer, ?_⟩
  dsimp [r0dot]
  rw [abs_mul, abs_of_pos hr0pos]
  calc
    r0 s * |b / 16 - adot / a s| ≤
        r0 s * ((Cb / 16 + Ca) * s ^ (-1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hr0pos.le
    _ = r0 s * (Cb / 16 + Ca) * s ^ (-1 : ℝ) := by ring

end HBL.TypeIIDynamicSelection
