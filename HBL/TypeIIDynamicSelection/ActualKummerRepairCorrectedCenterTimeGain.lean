import HBL.TypeIIDynamicSelection.ActualKummerRepairCenterTimeGainSqrtRadius
import Mathlib.Tactic

/-!
# Corrected-background quartic Hartree center gain

For the actual compact physical Kummer repair, the outer density is controlled
by P(A,D)=4 A^3 D+6 A^2 D^2+4 A D^3+D^4.  Adding a true current
correction of size e changes this quartic polynomial.  We retain *every*
mixed term: P(A+e,D)-P(A,D) is exactly e D times a positive polynomial.

Under the physical sqrt-clock shell X=O(s^(1/2)), the current source
jet D=O(s^(-rho)), and an actual correction e=O(s^(-rhoH)),
rhoH >= 1/2+kappa_center, the whole mixed density remains a next-layer
source of order rho+kappa_center.  No cancellation or free source-order label
is assumed.  The theorem is a pointwise center-budget producer; a complete
three-region parametrix still requires the genuine PDE field construction.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualKummerRepairCorrectedCrossCoefficient (W H J : ℝ) : ℝ :=
  12 * W ^ 2 + 12 * W * H + 4 * H ^ 2 +
    (12 * W + 6 * H) * J + 4 * J ^ 2

private theorem actual_Kummer_repair_cross_polynomial_exact
    (A e D : ℝ) :
    actualKummerRepairDensityPolynomial (A+e) D =
      actualKummerRepairDensityPolynomial A D +
        e * D * (12 * A ^ 2 + 12 * A * e + 4 * e ^ 2 +
          (12 * A + 6 * e) * D + 4 * D ^ 2) := by
  unfold actualKummerRepairDensityPolynomial
  ring

theorem actual_Kummer_repair_density_corrected_cross_bound
    (A e D W H J : ℝ)
    (hA : 0 ≤ A) (he : 0 ≤ e) (hD : 0 ≤ D)
    (_hW : 0 ≤ W) (_hH : 0 ≤ H) (_hJ : 0 ≤ J)
    (hAW : A ≤ W) (heH : e ≤ H) (hDJ : D ≤ J) :
    actualKummerRepairDensityPolynomial (A + e) D ≤
      actualKummerRepairDensityPolynomial A D +
        e * D * actualKummerRepairCorrectedCrossCoefficient W H J := by
  have hA2 : A ^ 2 ≤ W ^ 2 :=
    pow_le_pow_left₀ hA hAW 2
  have he2 : e ^ 2 ≤ H ^ 2 :=
    pow_le_pow_left₀ he heH 2
  have hD2 : D ^ 2 ≤ J ^ 2 :=
    pow_le_pow_left₀ hD hDJ 2
  have hAe : A * e ≤ W * H :=
    mul_le_mul hAW heH he (_hW)
  have hAD : A * D ≤ W * J :=
    mul_le_mul hAW hDJ hD (_hW)
  have heD : e * D ≤ H * J :=
    mul_le_mul heH hDJ hD (_hH)
  have hCoef :
      12 * A ^ 2 + 12 * A * e + 4 * e ^ 2 +
        (12 * A + 6 * e) * D + 4 * D ^ 2 ≤
      actualKummerRepairCorrectedCrossCoefficient W H J := by
    dsimp [actualKummerRepairCorrectedCrossCoefficient]
    nlinarith only [hA2, he2, hD2, hAe, hAD, heD]
  rw [actual_Kummer_repair_cross_polynomial_exact]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hCoef (mul_nonneg he hD)) _

theorem actual_Kummer_abstract_shell_envelope_le_sum
    (ell X M S : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hX : 0 ≤ X) (hM : 0 ≤ M) (hS : 0 ≤ S) :
    0 ≤ actualKummerRepairAbstractShellEnvelope ell X M S ∧
      actualKummerRepairAbstractShellEnvelope ell X M S ≤ M + S := by
  let m : ℝ := M / (1 + X)
  let z : ℝ := (S * Real.sqrt ell) / (1 + ell * X)
  have hden1 : 1 ≤ 1 + X := by linarith
  have hden2 : 1 ≤ 1 + ell * X := by
    have hprod := mul_nonneg hell.le hX
    linarith only [hprod]
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hm : m ≤ M := div_le_self hM hden1
  have hroot : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hz : z ≤ S := by
    calc
      z ≤ S * Real.sqrt ell := div_le_self
        (mul_nonneg hS (Real.sqrt_nonneg ell)) hden2
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hroot hS
      _ = S := by ring
  constructor
  · change 0 ≤ m + z
    positivity
  · change m + z ≤ M + S
    linarith only [hm, hz]

/-- Entire corrected-background quartic center budget.  No term of degree
2, 3 or 4 in the actual Kummer repair is discarded.  The extra correction
cross-terms gain the same locked positive shell order when rhoH is large
enough to offset the true sqrt-clock shell length. -/
theorem actual_Kummer_repair_corrected_full_center_sqrt_time_gain
    (ell X M S D e s beta rho rhoH CX CD CH : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hXlow : actualHartreeSlowInnerRadius ell ≤ X)
    (hXup : X ≤ CX * s ^ (1 / 2 : ℝ))
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (he : 0 ≤ e) (hCX : 0 ≤ CX) (hCD : 0 ≤ CD) (hCH : 0 ≤ CH)
    (hs : 1 ≤ s) (hbeta : 1 / 2 < beta)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (hrhoH : 1 / 2 + actualKummerRepairCenterTimeGain beta ≤ rhoH)
    (htrap : ell ≤ s ^ (-beta))
    (hDtime : D ≤ CD * s ^ (-rho))
    (heTime : e ≤ CH * s ^ (-rhoH)) :
    let A0 := actualKummerRepairAbstractShellEnvelope ell X M S
    let kc := actualKummerRepairCenterTimeGain beta
    let Ctime := 16 * (M ^ 3 + S ^ 3) * CD +
      12 * (M ^ 2 + S ^ 2) * CD ^ 2 +
      4 * M * CD ^ 3 + 4 * CX * S * CD ^ 3 + CX * CD ^ 4
    let Ccross := actualKummerRepairCorrectedCrossCoefficient
      (M + S) CH CD
    X * actualKummerRepairDensityPolynomial (A0 + e) D ≤
      (Ctime + CX * CH * CD * Ccross) * s ^ (-(rho + kc)) := by
  dsimp only
  let A0 := actualKummerRepairAbstractShellEnvelope ell X M S
  let kc := actualKummerRepairCenterTimeGain beta
  let Ctime := 16 * (M ^ 3 + S ^ 3) * CD +
      12 * (M ^ 2 + S ^ 2) * CD ^ 2 +
      4 * M * CD ^ 3 + 4 * CX * S * CD ^ 3 + CX * CD ^ 4
  let Ccross := actualKummerRepairCorrectedCrossCoefficient (M + S) CH CD
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hk : 0 < kc :=
    actual_Kummer_repair_center_time_gain_positive beta hbeta
  have hrhopos : 0 < rho := by
    have hEff : (1 / 2 + kc) / 2 ≤ rho := by
      simpa only [kc] using hrho
    linarith only [hEff, hk]
  have hrhoHpos : 0 < rhoH := by
    have hEff : 1 / 2 + kc ≤ rhoH := by
      simpa only [kc] using hrhoH
    linarith only [hEff, hk]
  have hX0 : 0 ≤ X := by
    have hL : 0 < actualHartreeSlowInnerRadius ell := by
      unfold actualHartreeSlowInnerRadius
      exact Real.rpow_pos_of_pos hell _
    exact (hL.trans_le hXlow).le
  have hA0 : 0 ≤ A0 ∧ A0 ≤ M + S := by
    simpa only [A0] using
      actual_Kummer_abstract_shell_envelope_le_sum
        ell X M S hell hellOne hX0 hM hS
  have hePowOne : s ^ (-rhoH) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have hDPowOne : s ^ (-rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have heCH : e ≤ CH := heTime.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hePowOne hCH)
  have hDCD : D ≤ CD := hDtime.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hDPowOne hCD)
  have hCross :=
    actual_Kummer_repair_density_corrected_cross_bound
      A0 e D (M + S) CH CD
      hA0.1 he hD (add_nonneg hM hS) hCH hCD hA0.2 heCH hDCD
  have hBaseRaw :=
    actual_Kummer_repair_full_center_time_gain_sqrt_radius
      ell X M S D s beta rho CX CD
      hell hellOne hXlow hXup hM hS hD hCX hCD
      hs hbeta hrho htrap hDtime
  have hBase :
      X * actualKummerRepairDensityPolynomial A0 D ≤
        Ctime * s ^ (-(rho + kc)) := by
    simpa only [A0, Ctime, kc] using hBaseRaw
  have hXpow : 0 ≤ CX * s ^ (1 / 2 : ℝ) :=
    mul_nonneg hCX (Real.rpow_nonneg hs0 _)
  have hePow : 0 ≤ CH * s ^ (-rhoH) :=
    mul_nonneg hCH (Real.rpow_nonneg hs0 _)
  have hXE :
      X * e ≤ (CX * s ^ (1 / 2 : ℝ)) * (CH * s ^ (-rhoH)) :=
    mul_le_mul hXup heTime he hXpow
  have hXED :
      (X * e) * D ≤
        ((CX * s ^ (1 / 2 : ℝ)) * (CH * s ^ (-rhoH))) *
          (CD * s ^ (-rho)) :=
    mul_le_mul hXE hDtime hD
      (mul_nonneg hXpow hePow)
  have hPow :
      (s ^ (1 / 2 : ℝ) * s ^ (-rhoH)) * s ^ (-rho) =
        s ^ (1 / 2 - rhoH - rho) := by
    rw [← Real.rpow_add hspos, ← Real.rpow_add hspos]
    congr 1
  have hExpo :
      s ^ (1 / 2 - rhoH - rho) ≤ s ^ (-(rho + kc)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by dsimp [kc] at hrhoH ⊢; linarith)
  have hCrossCoef : 0 ≤ Ccross := by
    dsimp [Ccross, actualKummerRepairCorrectedCrossCoefficient]
    positivity
  have hXEDtime :
      X * e * D ≤ (CX * CH * CD) * s ^ (-(rho + kc)) := by
    calc
      X * e * D ≤
          ((CX * s ^ (1 / 2 : ℝ)) * (CH * s ^ (-rhoH))) *
            (CD * s ^ (-rho)) := hXED
      _ = (CX * CH * CD) *
          ((s ^ (1 / 2 : ℝ) * s ^ (-rhoH)) * s ^ (-rho)) := by ring
      _ = (CX * CH * CD) * s ^ (1 / 2 - rhoH - rho) := by rw [hPow]
      _ ≤ (CX * CH * CD) * s ^ (-(rho + kc)) :=
        mul_le_mul_of_nonneg_left hExpo (by positivity)
  have hXEDcross :
      X * (e * D * Ccross) ≤
        (CX * CH * CD * Ccross) * s ^ (-(rho + kc)) := by
    calc
      _ = (X * e * D) * Ccross := by ring
      _ ≤ ((CX * CH * CD) * s ^ (-(rho + kc))) * Ccross :=
        mul_le_mul_of_nonneg_right hXEDtime hCrossCoef
      _ = (CX * CH * CD * Ccross) * s ^ (-(rho + kc)) := by ring
  calc
    X * actualKummerRepairDensityPolynomial (A0 + e) D ≤
        X * (actualKummerRepairDensityPolynomial A0 D + e * D * Ccross) :=
      mul_le_mul_of_nonneg_left hCross hX0
    _ = X * actualKummerRepairDensityPolynomial A0 D +
        X * (e * D * Ccross) := by ring
    _ ≤ Ctime * s ^ (-(rho + kc)) +
        (CX * CH * CD * Ccross) * s ^ (-(rho + kc)) :=
      add_le_add hBase hXEDcross
    _ = (Ctime + CX * CH * CD * Ccross) *
        s ^ (-(rho + kc)) := by ring

end HBL.TypeIIDynamicSelection
