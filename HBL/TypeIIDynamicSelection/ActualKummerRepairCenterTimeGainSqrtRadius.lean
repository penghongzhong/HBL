import HBL.TypeIIDynamicSelection.ActualKummerRepairCenterTimeGain
import Mathlib.Tactic

/-!
# Sharp physical sqrt-clock full Hartree Kummer center time gain

The actual Kummer coordinate obeys a²=q and the already certified trapped
clock gives q=O(s). Hence aR=O(s^(1/2)) for a fixed normalized R, not O(s).
Keeping the *full* quartic shell density polynomial (including D³,D⁴) now
permits a source of order rho to gain kappa_center whenever
  2 rho >= 1/2 + kappa_center,
rather than requiring rho>=1. No cancellation or prescribed Type-II rate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

private theorem actual_center_rpow_mul_nat
    (s rho : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    (s ^ (-rho)) ^ n = s ^ (-(n : ℝ) * rho) := by
  rw [← Real.rpow_mul_natCast hs (-rho) n]
  congr 1
  ring

/-- A purely quantitative time-order estimate for the FULL center polynomial.
No center cancellation is used. The positive gain is the safe minimum
min(beta/8,1/2), added to the current source order rho. -/
theorem actual_Kummer_repair_full_center_time_gain_sqrt_radius
    (ell X M S D s beta rho CX CD : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hXlow : actualHartreeSlowInnerRadius ell ≤ X)
    (hXup : X ≤ CX * s ^ (1 / 2 : ℝ))
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hCX : 0 ≤ CX) (hCD : 0 ≤ CD)
    (hs : 1 ≤ s) (hbeta : 1 / 2 < beta)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
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
  have hkpos : 0 < k := by
    dsimp [k]
    exact actual_Kummer_repair_center_time_gain_positive beta hbeta
  have hrhoEff : (1 / 2 + k) / 2 ≤ rho := by
    simpa only [k] using hrho
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hLpos : 0 < actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.rpow_pos_of_pos hell _
  have hX0 : 0 ≤ X := (hLpos.trans_le hXlow).le

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
        _ = _ := by congr 1; ring_nf
    exact h1.trans_eq h2

  have hD2 : D ^ 2 ≤ CD ^ 2 * s ^ (-2 * rho) := by
    have h := pow_le_pow_left₀ hD hDtime 2
    calc
      D ^ 2 ≤ (CD * s ^ (-rho)) ^ 2 := h
      _ = CD ^ 2 * (s ^ (-rho)) ^ 2 := by ring
      _ = CD ^ 2 * s ^ (-2 * rho) := by
        rw [actual_center_rpow_mul_nat s rho hs0 2]
        congr 2
  have hD3 : D ^ 3 ≤ CD ^ 3 * s ^ (-3 * rho) := by
    have h := pow_le_pow_left₀ hD hDtime 3
    calc
      D ^ 3 ≤ (CD * s ^ (-rho)) ^ 3 := h
      _ = CD ^ 3 * (s ^ (-rho)) ^ 3 := by ring
      _ = CD ^ 3 * s ^ (-3 * rho) := by
        rw [actual_center_rpow_mul_nat s rho hs0 3]
        congr 2
  have hD4 : D ^ 4 ≤ CD ^ 4 * s ^ (-4 * rho) := by
    have h := pow_le_pow_left₀ hD hDtime 4
    calc
      D ^ 4 ≤ (CD * s ^ (-rho)) ^ 4 := h
      _ = CD ^ 4 * (s ^ (-rho)) ^ 4 := by ring
      _ = CD ^ 4 * s ^ (-4 * rho) := by
        rw [actual_center_rpow_mul_nat s rho hs0 4]
        congr 2

  have hTargetBeta :
      s ^ (-(rho + beta / 8)) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hkBeta])
  have hTarget2 :
      s ^ (-2 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrhoEff, hkHalf, hkpos.le])
  have hTarget3 :
      s ^ (-3 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrhoEff, hkHalf, hkpos.le])
  have hTarget3s :
      s ^ (1 / 2 - 3 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrhoEff, hkHalf, hkpos.le])
  have hTarget4s :
      s ^ (1 / 2 - 4 * rho) ≤ s ^ (-(rho + k)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hrhoEff, hkHalf, hkpos.le])

  have hEllD :
      ell ^ (1 / 8 : ℝ) * D ≤
        CD * s ^ (-(rho + k)) := by
    have hprod :
        ell ^ (1 / 8 : ℝ) * D ≤
          s ^ (-(beta / 8)) * (CD * s ^ (-rho)) :=
      mul_le_mul hell18 hDtime hD (Real.rpow_nonneg hs0 _)
    calc
      _ ≤ s ^ (-(beta / 8)) * (CD * s ^ (-rho)) := hprod
      _ = CD * (s ^ (-(beta / 8)) * s ^ (-rho)) := by ring
      _ = CD * s ^ (-(beta / 8) + (-rho)) := by
        rw [← Real.rpow_add hspos]
      _ = CD * s ^ (-(rho + beta / 8)) := by
        congr 2
        ring
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
      s ^ (1 / 2 : ℝ) * D ^ 3 ≤ CD ^ 3 * s ^ (1 / 2 - 3 * rho) := by
    calc
      s ^ (1 / 2 : ℝ) * D ^ 3 ≤ s * (CD ^ 3 * s ^ (-3 * rho)) :=
        mul_le_mul_of_nonneg_left hD3 hs0
      _ = CD ^ 3 * (s ^ (1 / 2 : ℝ) * s ^ (-3 * rho)) := by
        ring
      _ = CD ^ 3 * s ^ (1 / 2 - 3 * rho) := by
        rw [← Real.rpow_add hspos]
        congr 1; ring_nf
  have hsD3t :
      s ^ (1 / 2 : ℝ) * D ^ 3 ≤ CD ^ 3 * s ^ (-(rho + k)) :=
    hsD3.trans
      (mul_le_mul_of_nonneg_left hTarget3s (pow_nonneg hCD 3))

  have hsD4 :
      s ^ (1 / 2 : ℝ) * D ^ 4 ≤ CD ^ 4 * s ^ (1 / 2 - 4 * rho) := by
    calc
      s ^ (1 / 2 : ℝ) * D ^ 4 ≤ s * (CD ^ 4 * s ^ (-4 * rho)) :=
        mul_le_mul_of_nonneg_left hD4 hs0
      _ = CD ^ 4 * (s ^ (1 / 2 : ℝ) * s ^ (-4 * rho)) := by
        ring
      _ = CD ^ 4 * s ^ (1 / 2 - 4 * rho) := by
        rw [← Real.rpow_add hspos]
        congr 1; ring_nf
  have hsD4t :
      s ^ (1 / 2 : ℝ) * D ^ 4 ≤ CD ^ 4 * s ^ (-(rho + k)) :=
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
          (by
            calc
              16 * (M ^ 3 + S ^ 3) * ell ^ (1 / 8 : ℝ) * D =
                  (16 * (M ^ 3 + S ^ 3)) *
                    (ell ^ (1 / 8 : ℝ) * D) := by ring
              _ ≤ (16 * (M ^ 3 + S ^ 3)) *
                    (CD * s ^ (-(rho + k))) :=
                  mul_le_mul_of_nonneg_left hEllD hC3)
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
        CX * S * s ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ X * S := mul_le_mul_of_nonneg_left hRadFrac hX0
      _ ≤ (CX * s ^ (1 / 2 : ℝ)) * S :=
        mul_le_mul_of_nonneg_right hXup hS
      _ = CX * S * s ^ (1 / 2 : ℝ) := by ring
  have hXA :
      X * A0 ≤ M + CX * S * s ^ (1 / 2 : ℝ) := by
    dsimp [A0, actualKummerRepairAbstractShellEnvelope]
    calc
      X * (M / (1 + X) + (S * Real.sqrt ell) / (1 + ell * X)) =
          X * (M / (1 + X)) +
            X * ((S * Real.sqrt ell) / (1 + ell * X)) := by ring
      _ ≤ M + CX * S * s ^ (1 / 2 : ℝ) := add_le_add hMono hRad

  have hHighCubic :
      X * (4 * A0 * D ^ 3) ≤
        (4 * M * CD ^ 3 + 4 * CX * S * CD ^ 3) *
          s ^ (-(rho + k)) := by
    have h4D : 0 ≤ 4 * D ^ 3 := by positivity
    calc
      _ = 4 * (X * A0) * D ^ 3 := by ring
      _ ≤ 4 * (M + CX * S * s ^ (1 / 2 : ℝ)) * D ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXA (by norm_num)) (pow_nonneg hD 3)
      _ = 4 * M * D ^ 3 + 4 * CX * S * (s ^ (1 / 2 : ℝ) * D ^ 3) := by ring
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
      X * D ^ 4 ≤ (CX * s ^ (1 / 2 : ℝ)) * D ^ 4 :=
        mul_le_mul_of_nonneg_right hXup (pow_nonneg hD 4)
      _ = CX * (s ^ (1 / 2 : ℝ) * D ^ 4) := by ring
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
