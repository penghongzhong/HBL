import HBL.TypeIIDynamicSelection.ActualKummerRepairCenterBudget
import HBL.TypeIIDynamicSelection.ActualKummerRepairFullDensityFeedback
import Mathlib.Tactic

/-!
# Full Kummer-repair center feedback has a strict time gain

The complete exterior-center density polynomial is
  X * P(A,D),  P=4 A^3 D + 6 A^2 D^2 + 4 A D^3 + D^4.

The strict low-degree shell budget already controls the first two terms.
For the last two terms we use only:
* the current profile order D = O(s^(-rho)), rho >= 1;
* a coarse physical Kummer-radius growth X = O(s);
* the one-sided scale trap ell <= s^(-beta), beta > 1/2.

The coarse X=O(s) is intentionally much weaker than the final selected
Type-II rate and can be supplied from the linear q-clock trap.  No limiting
mu or blowup exponent occurs here.
The strict clock-to-radius producer is kept in ActualKummerRepairClockRadius and will be composed downstream.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualKummerRepairCenterTimeGain (beta : ℝ) : ℝ :=
  min (beta / 8) (1 / 2)

theorem actual_Kummer_repair_center_time_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    0 < actualKummerRepairCenterTimeGain beta := by
  unfold actualKummerRepairCenterTimeGain
  exact lt_min (by linarith) (by norm_num)

private theorem actual_center_rpow_mul_nat
    (s rho : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    (s ^ (-rho)) ^ n = s ^ (-(n : ℝ) * rho) := by
  rw [← Real.rpow_mul_natCast hs (-rho) n]
  congr 1
  ring

/-- A purely quantitative time-order estimate for the FULL center polynomial.
No center cancellation is used. The positive gain is the safe minimum
min(beta/8,1/2), added to the current source order rho. -/
theorem actual_Kummer_repair_full_center_time_gain
    (ell X M S D s beta rho CX CD : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hXlow : actualHartreeSlowInnerRadius ell ≤ X)
    (hXup : X ≤ CX * s)
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hCX : 0 ≤ CX) (hCD : 0 ≤ CD)
    (hs : 1 ≤ s) (_hbeta : 1 / 2 < beta) (hrho : 1 ≤ rho)
    (htrap : ell ≤ s ^ (-beta))
    (hDtime : D ≤ CD * s ^ (-rho)) :
    let A0 := actualKummerRepairAbstractShellEnvelope ell X M S
    let P := actualKummerRepairDensityPolynomial A0 D
    let k := actualKummerRepairCenterTimeGain beta
    X * P ≤
      (16 * (M ^ 3 + S ^ 3) * CD +
        12 * (M ^ 2 + S ^ 2) * CD ^ 2 +
        4 * M * CD ^ 3 +
        4 * CX * S * CD ^ 3 +
        CX * CD ^ 4) *
        s ^ (-(rho + k)) := by
  dsimp only
  let A0 := actualKummerRepairAbstractShellEnvelope ell X M S
  let k := actualKummerRepairCenterTimeGain beta
  have hkBeta : k ≤ beta / 8 := by
    dsimp [k, actualKummerRepairCenterTimeGain]
    exact min_le_left _ _
  have hkHalf : k ≤ 1 / 2 := by
    dsimp [k, actualKummerRepairCenterTimeGain]
    exact min_le_right _ _
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hLpos : 0 < actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.rpow_pos_of_pos hell _
  have hX0 : 0 ≤ X := (hLpos.trans_le hXlow).le
  have hDtop : 0 ≤ CD * s ^ (-rho) :=
    mul_nonneg hCD (Real.rpow_nonneg hs0 _)

  have hell18 :
      ell ^ (1 / 8 : ℝ) ≤ s ^ (-(beta / 8)) := by
    have h1 : ell ^ (1 / 8 : ℝ) ≤
        (s ^ (-beta)) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow hell.le htrap (by norm_num)
    have h2 : (s ^ (-beta)) ^ (1 / 8 : ℝ) =
        s ^ (-(beta / 8)) := by
      calc
        _ = s ^ ((-beta) * (1 / 8 : ℝ)) :=
          (Real.rpow_mul hs0 (-beta) (1 / 8 : ℝ)).symm
        _ = _ := by congr 1 <;> ring
    exact h1.trans_eq h2

  have hD2 : D ^ 2 ≤ CD ^ 2 * s ^ (-2 * rho) := by
    have h := pow_le_pow_left₀ hD hDtime 2
    calc
      D ^ 2 ≤ (CD * s ^ (-rho)) ^ 2 := h
      _ = CD ^ 2 * (s ^ (-rho)) ^ 2 := by ring
      _ = CD ^ 2 * s ^ (-2 * rho) := by
        rw [actual_center_rpow_mul_nat s rho hs0 2]
        congr 2
        ring
  have hD3 : D ^ 3 ≤ CD ^ 3 * s ^ (-3 * rho) := by
    have h := pow_le_pow_left₀ hD hDtime 3
    calc
      D ^ 3 ≤ (CD * s ^ (-rho)) ^ 3 := h
      _ = CD ^ 3 * (s ^ (-rho)) ^ 3 := by ring
      _ = CD ^ 3 * s ^ (-3 * rho) := by
        rw [actual_center_rpow_mul_nat s rho hs0 3]
        congr 2
        ring
  have hD4 : D ^ 4 ≤ CD ^ 4 * s ^ (-4 * rho) := by
    have h := pow_le_pow_left₀ hD hDtime 4
    calc
      D ^ 4 ≤ (CD * s ^ (-rho)) ^ 4 := h
      _ = CD ^ 4 * (s ^ (-rho)) ^ 4 := by ring
      _ = CD ^ 4 * s ^ (-4 * rho) := by
        rw [actual_center_rpow_mul_nat s rho hs0 4]
        congr 2
        ring

  have hTargetBeta :
      s ^ (-(rho + beta / 8)) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hkBeta])
  have hTarget2 :
      s ^ (-2 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrho, hkHalf])
  have hTarget3 :
      s ^ (-3 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrho, hkHalf])
  have hTarget3s :
      s ^ (1 - 3 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrho, hkHalf])
  have hTarget4s :
      s ^ (1 - 4 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrho, hkHalf])

  have hEllD :
      ell ^ (1 / 8 : ℝ) * D ≤
        CD * s ^ (-(rho + k)) := by
    have hprod :
        ell ^ (1 / 8 : ℝ) * D ≤
          s ^ (-(beta / 8)) * (CD * s ^ (-rho)) :=
      mul_le_mul hell18 hDtime hD hDtop
    calc
      _ ≤ s ^ (-(beta / 8)) * (CD * s ^ (-rho)) := hprod
      _ = CD * s ^ (-(rho + beta / 8)) := by
        rw [← Real.rpow_add hspos]
        congr 1 <;> ring
      _ ≤ CD * s ^ (-(rho + k)) :=
        mul_le_mul_of_nonneg_left hTargetBeta hCD

  have hD2t :
      D ^ 2 ≤ CD ^ 2 * s ^ (-(rho + k)) :=
    hD2.trans
      (mul_le_mul_of_nonneg_left hTarget2 (sq_nonneg CD))
  have hD3t :
      D ^ 3 ≤ CD ^ 3 * s ^ (-(rho + k)) :=
    hD3.trans
      (mul_le_mul_of_nonneg_left hTarget3 (pow_nonneg hCD 3))

  have hsD3 :
      s * D ^ 3 ≤ CD ^ 3 * s ^ (1 - 3 * rho) := by
    calc
      s * D ^ 3 ≤ s * (CD ^ 3 * s ^ (-3 * rho)) :=
        mul_le_mul_of_nonneg_left hD3 hs0
      _ = CD ^ 3 * (s ^ (1 : ℝ) * s ^ (-3 * rho)) := by
        rw [Real.rpow_one]
        ring
      _ = CD ^ 3 * s ^ (1 - 3 * rho) := by
        rw [← Real.rpow_add hspos]
        congr 1 <;> ring
  have hsD3t :
      s * D ^ 3 ≤ CD ^ 3 * s ^ (-(rho + k)) :=
    hsD3.trans
      (mul_le_mul_of_nonneg_left hTarget3s (pow_nonneg hCD 3))

  have hsD4 :
      s * D ^ 4 ≤ CD ^ 4 * s ^ (1 - 4 * rho) := by
    calc
      s * D ^ 4 ≤ s * (CD ^ 4 * s ^ (-4 * rho)) :=
        mul_le_mul_of_nonneg_left hD4 hs0
      _ = CD ^ 4 * (s ^ (1 : ℝ) * s ^ (-4 * rho)) := by
        rw [Real.rpow_one]
        ring
      _ = CD ^ 4 * s ^ (1 - 4 * rho) := by
        rw [← Real.rpow_add hspos]
        congr 1 <;> ring
  have hsD4t :
      s * D ^ 4 ≤ CD ^ 4 * s ^ (-(rho + k)) :=
    hsD4.trans
      (mul_le_mul_of_nonneg_left hTarget4s (pow_nonneg hCD 4))

  have hLow :=
    actual_Kummer_repair_center_linear_quadratic_budget
      ell X M S D hell hellOne hXlow hM hS hD
  have hLowT :
      X * (4 * A0 ^ 3 * D + 6 * A0 ^ 2 * D ^ 2) ≤
        (16 * (M ^ 3 + S ^ 3) * CD +
          12 * (M ^ 2 + S ^ 2) * CD ^ 2) *
          s ^ (-(rho + k)) := by
    have hC3 : 0 ≤ 16 * (M ^ 3 + S ^ 3) := by positivity
    have hC2 : 0 ≤ 12 * (M ^ 2 + S ^ 2) := by positivity
    calc
      _ ≤ 16 * (M ^ 3 + S ^ 3) * ell ^ (1 / 8 : ℝ) * D +
          12 * (M ^ 2 + S ^ 2) * D ^ 2 := by
        simpa only [A0] using hLow
      _ ≤ 16 * (M ^ 3 + S ^ 3) *
            (CD * s ^ (-(rho + k))) +
          12 * (M ^ 2 + S ^ 2) *
            (CD ^ 2 * s ^ (-(rho + k))) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hEllD hC3)
          (mul_le_mul_of_nonneg_left hD2t hC2)
      _ = _ := by ring

  have hden1 : 0 < 1 + X := by linarith
  have hMono :
      X * (M / (1 + X)) ≤ M := by
    calc
      X * (M / (1 + X)) = (M * X) / (1 + X) := by ring
      _ ≤ M := by
        apply (div_le_iff₀ hden1).2
        nlinarith [mul_nonneg hM hX0]
  have hsqrtOne : Real.sqrt ell ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hellOne
  have hdenRad : 1 ≤ 1 + ell * X := by
    nlinarith [mul_nonneg hell.le hX0]
  have hRadFrac :
      (S * Real.sqrt ell) / (1 + ell * X) ≤ S := by
    have hnum : 0 ≤ S * Real.sqrt ell :=
      mul_nonneg hS (Real.sqrt_nonneg ell)
    calc
      _ ≤ S * Real.sqrt ell := div_le_self hnum hdenRad
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hsqrtOne hS
      _ = S := by ring
  have hRad :
      X * ((S * Real.sqrt ell) / (1 + ell * X)) ≤
        CX * S * s := by
    calc
      _ ≤ X * S := mul_le_mul_of_nonneg_left hRadFrac hX0
      _ ≤ (CX * s) * S :=
        mul_le_mul_of_nonneg_right hXup hS
      _ = CX * S * s := by ring
  have hXA :
      X * A0 ≤ M + CX * S * s := by
    dsimp [A0, actualKummerRepairAbstractShellEnvelope]
    calc
      X * (M / (1 + X) + (S * Real.sqrt ell) / (1 + ell * X)) =
          X * (M / (1 + X)) +
            X * ((S * Real.sqrt ell) / (1 + ell * X)) := by ring
      _ ≤ M + CX * S * s := add_le_add hMono hRad

  have hHighCubic :
      X * (4 * A0 * D ^ 3) ≤
        (4 * M * CD ^ 3 + 4 * CX * S * CD ^ 3) *
          s ^ (-(rho + k)) := by
    have h4D : 0 ≤ 4 * D ^ 3 := by positivity
    calc
      _ = 4 * (X * A0) * D ^ 3 := by ring
      _ ≤ 4 * (M + CX * S * s) * D ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXA (by norm_num)) (pow_nonneg hD 3)
      _ = 4 * M * D ^ 3 + 4 * CX * S * (s * D ^ 3) := by ring
      _ ≤ 4 * M * (CD ^ 3 * s ^ (-(rho + k))) +
          4 * CX * S * (CD ^ 3 * s ^ (-(rho + k))) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hD3t (by positivity))
          (mul_le_mul_of_nonneg_left hsD3t (by positivity))
      _ = _ := by ring

  have hHighQuartic :
      X * D ^ 4 ≤
        (CX * CD ^ 4) * s ^ (-(rho + k)) := by
    calc
      X * D ^ 4 ≤ (CX * s) * D ^ 4 :=
        mul_le_mul_of_nonneg_right hXup (pow_nonneg hD 4)
      _ = CX * (s * D ^ 4) := by ring
      _ ≤ CX * (CD ^ 4 * s ^ (-(rho + k))) :=
        mul_le_mul_of_nonneg_left hsD4t hCX
      _ = _ := by ring

  have hSplit :
      X * actualKummerRepairDensityPolynomial A0 D =
        X * (4 * A0 ^ 3 * D + 6 * A0 ^ 2 * D ^ 2) +
          X * (4 * A0 * D ^ 3) + X * D ^ 4 := by
    unfold actualKummerRepairDensityPolynomial
    ring
  rw [hSplit]
  calc
    _ ≤ ((16 * (M ^ 3 + S ^ 3) * CD +
          12 * (M ^ 2 + S ^ 2) * CD ^ 2) *
          s ^ (-(rho + k))) +
        ((4 * M * CD ^ 3 + 4 * CX * S * CD ^ 3) *
          s ^ (-(rho + k))) +
        ((CX * CD ^ 4) * s ^ (-(rho + k))) :=
      add_le_add (add_le_add hLowT hHighCubic) hHighQuartic
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
