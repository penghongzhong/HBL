import HBL.TypeIIDynamicSelection.ActualKummerRepairBackgroundEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import Mathlib.Tactic

/-!
# Low-degree center budget on the true Kummer repair shell

Let X=aR and L=ell^(-1/16).  If X>=L, the true background shell envelope
splits into
  M/(1+X) + S*sqrt(ell)/(1+ell*X).

The cubic background factor gains ell^(1/8), while the quadratic factor is
uniform.  Consequently the linear and quadratic terms in the complete
quartic repair-density center are already harmless:
  X*4*A^3*D = O(ell^(1/8) D),
  X*6*A^2*D^2 = O(D^2).

The cubic-in-D and pure D^4 center terms are intentionally NOT estimated
here.  They remain the genuine remote/center-matching obligation.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualKummerRepairAbstractShellEnvelope
    (ell X M S : ℝ) : ℝ :=
  M / (1 + X) + (S * Real.sqrt ell) / (1 + ell * X)

theorem actual_Kummer_repair_abstract_shell_envelope_nonneg
    (ell X M S : ℝ)
    (hell : 0 < ell) (hX : 0 ≤ X) (hM : 0 ≤ M) (hS : 0 ≤ S) :
    0 ≤ actualKummerRepairAbstractShellEnvelope ell X M S := by
  unfold actualKummerRepairAbstractShellEnvelope
  positivity

private theorem actual_repair_shell_mono_square
    (ell X M : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hX : actualHartreeSlowInnerRadius ell ≤ X)
    (hM : 0 ≤ M) :
    X * (M / (1 + X)) ^ 2 ≤ M ^ 2 := by
  have hLone : 1 ≤ actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hell hellOne (by norm_num)
  have hXone : 1 ≤ X := hLone.trans hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hfrac : M / (1 + X) ≤ M / X :=
    div_le_div_of_nonneg_left hM hXpos (by linarith)
  have hfrac0 : 0 ≤ M / (1 + X) := by positivity
  have hsq := pow_le_pow_left₀ hfrac0 hfrac 2
  calc
    X * (M / (1 + X)) ^ 2 ≤ X * (M / X) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hXpos.le
    _ = M ^ 2 / X := by field_simp [hXpos.ne']; ring
    _ ≤ M ^ 2 := div_le_self (sq_nonneg M) hXone

private theorem actual_repair_shell_radiation_square
    (ell X S : ℝ)
    (hell : 0 < ell) (hX : 0 ≤ X) (hS : 0 ≤ S) :
    X * ((S * Real.sqrt ell) / (1 + ell * X)) ^ 2 ≤ S ^ 2 := by
  let t : ℝ := ell * X
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hden : 0 < 1 + t := by linarith
  have htBound : t ≤ (1 + t) ^ 2 := by
    nlinarith [sq_nonneg t]
  have hratio : t / (1 + t) ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hden)).2 htBound
  have hsq : (Real.sqrt ell) ^ 2 = ell :=
    Real.sq_sqrt hell.le
  have hEq :
      X * ((S * Real.sqrt ell) / (1 + ell * X)) ^ 2 =
        S ^ 2 * (t / (1 + t) ^ 2) := by
    dsimp [t]
    rw [div_pow, mul_pow, hsq]
    field_simp [hden.ne']
  rw [hEq]
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  exact (mul_le_mul_of_nonneg_left hratio hS2).trans_eq (mul_one _)

private theorem actual_repair_shell_mono_cube
    (ell X M : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hX : actualHartreeSlowInnerRadius ell ≤ X)
    (hM : 0 ≤ M) :
    X * (M / (1 + X)) ^ 3 ≤ M ^ 3 * ell ^ (1 / 8 : ℝ) := by
  let L : ℝ := actualHartreeSlowInnerRadius ell
  have hLpos : 0 < L := by
    dsimp [L, actualHartreeSlowInnerRadius]
    exact Real.rpow_pos_of_pos hell _
  have hLone : 1 ≤ L := by
    dsimp [L, actualHartreeSlowInnerRadius]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hell hellOne (by norm_num)
  have hXone : 1 ≤ X := hLone.trans hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hfrac : M / (1 + X) ≤ M / X :=
    div_le_div_of_nonneg_left hM hXpos (by linarith)
  have hfrac0 : 0 ≤ M / (1 + X) := by positivity
  have hcub := pow_le_pow_left₀ hfrac0 hfrac 3
  have hFirst :
      X * (M / (1 + X)) ^ 3 ≤ M ^ 3 / X ^ 2 := by
    calc
      _ ≤ X * (M / X) ^ 3 :=
        mul_le_mul_of_nonneg_left hcub hXpos.le
      _ = M ^ 3 / X ^ 2 := by field_simp [hXpos.ne']
  have hLsq : L ^ 2 ≤ X ^ 2 :=
    pow_le_pow_left₀ hLpos.le hX 2
  have hInv :
      1 / X ^ 2 ≤ 1 / L ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 2) hLsq
  have hLpow : L ^ 2 = ell ^ (-(1 / 8 : ℝ)) := by
    dsimp [L, actualHartreeSlowInnerRadius]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hell.le]
    norm_num
  have hInvL : 1 / L ^ 2 = ell ^ (1 / 8 : ℝ) := by
    rw [hLpow, Real.rpow_neg hell.le (1 / 8 : ℝ)]
    simp [one_div]
  have hInvX : 1 / X ^ 2 ≤ ell ^ (1 / 8 : ℝ) :=
    hInv.trans_eq hInvL
  calc
    X * (M / (1 + X)) ^ 3 ≤ M ^ 3 / X ^ 2 := hFirst
    _ = M ^ 3 * (1 / X ^ 2) := by ring
    _ ≤ M ^ 3 * ell ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hInvX (pow_nonneg hM 3)

private theorem actual_repair_shell_radiation_cube
    (ell X S : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hX : 0 ≤ X) (hS : 0 ≤ S) :
    X * ((S * Real.sqrt ell) / (1 + ell * X)) ^ 3 ≤
      S ^ 3 * ell ^ (1 / 8 : ℝ) := by
  let t : ℝ := ell * X
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hden : 0 < 1 + t := by linarith
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have htBound : t ≤ (1 + t) ^ 3 := by
    nlinarith [sq_nonneg t, ht3]
  have hratio : t / (1 + t) ^ 3 ≤ 1 :=
    (div_le_one (pow_pos hden 3)).2 htBound
  have hsq : (Real.sqrt ell) ^ 2 = ell :=
    Real.sq_sqrt hell.le
  have hsqrt3 :
      (Real.sqrt ell) ^ 3 = ell * Real.sqrt ell := by
    calc
      (Real.sqrt ell) ^ 3 =
          (Real.sqrt ell) ^ 2 * Real.sqrt ell := by ring
      _ = ell * Real.sqrt ell := by rw [hsq]
  have hEq :
      X * ((S * Real.sqrt ell) / (1 + ell * X)) ^ 3 =
        S ^ 3 * Real.sqrt ell * (t / (1 + t) ^ 3) := by
    dsimp [t]
    rw [div_pow, mul_pow, hsqrt3]
    field_simp [hden.ne']
    ring
  have hsqrt :
      Real.sqrt ell ≤ ell ^ (1 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge
      hell hellOne (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)
  have hS3 : 0 ≤ S ^ 3 := pow_nonneg hS 3
  calc
    _ = S ^ 3 * Real.sqrt ell * (t / (1 + t) ^ 3) := hEq
    _ ≤ S ^ 3 * Real.sqrt ell * 1 :=
      mul_le_mul_of_nonneg_left hratio
        (mul_nonneg hS3 (Real.sqrt_nonneg ell))
    _ = S ^ 3 * Real.sqrt ell := by ring
    _ ≤ S ^ 3 * ell ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt hS3

theorem actual_Kummer_repair_shell_background_square_budget
    (ell X M S : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hX : actualHartreeSlowInnerRadius ell ≤ X)
    (hM : 0 ≤ M) (hS : 0 ≤ S) :
    X * (actualKummerRepairAbstractShellEnvelope ell X M S) ^ 2 ≤
      2 * (M ^ 2 + S ^ 2) := by
  let m : ℝ := M / (1 + X)
  let z : ℝ := (S * Real.sqrt ell) / (1 + ell * X)
  have hLpos : 0 < actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.rpow_pos_of_pos hell _
  have hX0 : 0 ≤ X := (hLpos.trans_le hX).le
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hsum :
      (m + z) ^ 2 ≤ 2 * (m ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (m - z)]
  have hm2 := actual_repair_shell_mono_square ell X M hell hellOne hX hM
  have hz2 := actual_repair_shell_radiation_square ell X S hell hX0 hS
  calc
    X * (actualKummerRepairAbstractShellEnvelope ell X M S) ^ 2 =
        X * (m + z) ^ 2 := by
      dsimp [actualKummerRepairAbstractShellEnvelope, m, z]
    _ ≤ X * (2 * (m ^ 2 + z ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum hX0
    _ = 2 * (X * m ^ 2 + X * z ^ 2) := by ring
    _ ≤ 2 * (M ^ 2 + S ^ 2) := by
      nlinarith only [hm2, hz2]

theorem actual_Kummer_repair_shell_background_cube_budget
    (ell X M S : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hX : actualHartreeSlowInnerRadius ell ≤ X)
    (hM : 0 ≤ M) (hS : 0 ≤ S) :
    X * (actualKummerRepairAbstractShellEnvelope ell X M S) ^ 3 ≤
      4 * (M ^ 3 + S ^ 3) * ell ^ (1 / 8 : ℝ) := by
  let m : ℝ := M / (1 + X)
  let z : ℝ := (S * Real.sqrt ell) / (1 + ell * X)
  have hLpos : 0 < actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.rpow_pos_of_pos hell _
  have hX0 : 0 ≤ X := (hLpos.trans_le hX).le
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hsum :
      (m + z) ^ 3 ≤ 4 * (m ^ 3 + z ^ 3) := by
    have hpos : 0 ≤ 3 * (m + z) * (m - z) ^ 2 := by positivity
    nlinarith
  have hm3 := actual_repair_shell_mono_cube ell X M hell hellOne hX hM
  have hz3 := actual_repair_shell_radiation_cube ell X S hell hellOne hX0 hS
  calc
    X * (actualKummerRepairAbstractShellEnvelope ell X M S) ^ 3 =
        X * (m + z) ^ 3 := by
      dsimp [actualKummerRepairAbstractShellEnvelope, m, z]
    _ ≤ X * (4 * (m ^ 3 + z ^ 3)) :=
      mul_le_mul_of_nonneg_left hsum hX0
    _ = 4 * (X * m ^ 3 + X * z ^ 3) := by ring
    _ ≤ 4 * ((M ^ 3 * ell ^ (1 / 8 : ℝ)) +
        (S ^ 3 * ell ^ (1 / 8 : ℝ))) := by
      nlinarith only [hm3, hz3]
    _ = 4 * (M ^ 3 + S ^ 3) * ell ^ (1 / 8 : ℝ) := by ring

/-- Exactly the low-degree part of X*P(A,D).  The D^3 and D^4 center
terms are excluded from the conclusion and remain to be handled by the
remote/center channel. -/
theorem actual_Kummer_repair_center_linear_quadratic_budget
    (ell X M S D : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hX : actualHartreeSlowInnerRadius ell ≤ X)
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    let A0 := actualKummerRepairAbstractShellEnvelope ell X M S
    X * (4 * A0 ^ 3 * D + 6 * A0 ^ 2 * D ^ 2) ≤
      16 * (M ^ 3 + S ^ 3) * ell ^ (1 / 8 : ℝ) * D +
        12 * (M ^ 2 + S ^ 2) * D ^ 2 := by
  dsimp only
  let A0 := actualKummerRepairAbstractShellEnvelope ell X M S
  have h3 :=
    actual_Kummer_repair_shell_background_cube_budget
      ell X M S hell hellOne hX hM hS
  have h2 :=
    actual_Kummer_repair_shell_background_square_budget
      ell X M S hell hellOne hX hM hS
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  calc
    X * (4 * A0 ^ 3 * D + 6 * A0 ^ 2 * D ^ 2) =
        4 * (X * A0 ^ 3) * D + 6 * (X * A0 ^ 2) * D ^ 2 := by ring
    _ ≤ 4 * (4 * (M ^ 3 + S ^ 3) * ell ^ (1 / 8 : ℝ)) * D +
        6 * (2 * (M ^ 2 + S ^ 2)) * D ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 (by norm_num)) hD)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h2 (by norm_num)) hD2)
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
