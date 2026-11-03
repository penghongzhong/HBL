import HBL.TypeIIDynamicSelection.ActualHartreeWeightedPositiveOrder
import Mathlib.Tactic

/-!
# Revised HBL 2.13: limiting genuine Hartree nonlinear source power

For 0<ell<=1, r>=0, set d=1+r and q=1+ell*r.
The physically scaled Strauss radiation is bounded by
  |Z_ell(r)| <= E sqrt(ell)/q.
The true core Riesz potential's PDE-derived Taylor error is O(ell).

The worst cubic term in the ORIGINAL energy-critical Hartree nonlocal
source is therefore the physical core-potential error times Z_ell^3.
In the admissible Fredholm weight sigma=7/4, its envelope is
  ell^(5/2) d^(7/4)/q^3.
A short exact real-power inequality proves
  ell^(5/2) d^(7/4)/q^3
     <= ell^(1/8) d^(-5/8).

Since d^(-5/8) belongs to L2(0,infinity), this gives a strict
positive length order with no hypothesis on the Type-II blowup
time rate, no generated-term assigned order, and no new axiom.

The other genuine nonlinear monomials have equal or stronger powers;
their complete finite enumeration and the parameter/three-region
profile are separate manuscript obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail

/-- The actual Japanese weight at sigma=7/4 is bounded by the ordinary
physical radius power (1+r)^(7/4). -/
theorem actual_Hartree_fredholm_seven_quarters_weight_radial
    (r : ℝ) (hr : 0 ≤ r) :
    affineJapaneseWeight (7 / 4 : ℝ) r ≤
      (1 + r) ^ (7 / 4 : ℝ) := by
  let d : ℝ := 1 + r
  have hd : 0 < d := by dsimp [d]; linarith
  have hGeom : 1 + r ^ 2 ≤ d ^ 2 := by
    dsimp [d]
    nlinarith [hr]
  have hPow :
      (1 + r ^ 2) ^ (7 / 8 : ℝ) ≤
        (d ^ 2) ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hGeom (by norm_num)
  have hRight :
      (d ^ 2) ^ (7 / 8 : ℝ) = d ^ (7 / 4 : ℝ) := by
    calc
      (d ^ 2) ^ (7 / 8 : ℝ) =
          d ^ ((2 : ℝ) * (7 / 8 : ℝ)) := by
            simpa only [Real.rpow_natCast] using
              (Real.rpow_mul hd.le (2 : ℝ) (7 / 8 : ℝ)).symm
      _ = d ^ (7 / 4 : ℝ) := by norm_num
  change (1 + r ^ 2) ^ ((7 / 4 : ℝ) / 2) ≤
    (1 + r) ^ (7 / 4 : ℝ)
  convert hPow.trans_eq hRight using 1 <;> norm_num

/-- The limiting original Hartree source weight (one ell-length
core-potential error times three genuinely critically scaled complex
radiation factors) has at least 1/8 strictly positive length gain.
This is an elementary but nontrivial radial-space/critical-scale
inequality, with no assumed time or blowup rate. -/
theorem actual_Hartree_true_source_worst_cubic_one_eighth_gain
    (ell r : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 ≤ r) :
    ell ^ (5 / 2 : ℝ) * (1 + r) ^ (7 / 4 : ℝ) /
        (1 + ell * r) ^ 3 ≤
      ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by
  let d : ℝ := 1 + r
  let q : ℝ := 1 + ell * r
  have hd : 0 < d := by dsimp [d]; linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hqOne : 1 ≤ q := by
    dsimp [q]
    nlinarith [mul_nonneg hell.le hr]
  have hScale : ell * d ≤ q := by
    dsimp [d,q]
    nlinarith [hellOne]
  have hScaledPow :
      ell ^ (19 / 8 : ℝ) * d ^ (19 / 8 : ℝ) ≤ q ^ 3 := by
    calc
      ell ^ (19 / 8 : ℝ) * d ^ (19 / 8 : ℝ) =
          (ell * d) ^ (19 / 8 : ℝ) :=
        (Real.mul_rpow hell.le hd.le).symm
      _ ≤ q ^ (19 / 8 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hScale (by norm_num)
      _ ≤ q ^ 3 := by
        have hStep := Real.rpow_le_rpow_of_exponent_le hqOne
          (show (19 / 8 : ℝ) ≤ 3 by norm_num)
        exact hStep.trans_eq (Real.rpow_natCast q 3)
  have hEllPow :
      ell ^ (5 / 2 : ℝ) =
        ell ^ (1 / 8 : ℝ) * ell ^ (19 / 8 : ℝ) := by
    calc
      _ = ell ^ ((1 / 8 : ℝ) + (19 / 8 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hell _ _
  have hRadiusPow :
      d ^ (7 / 4 : ℝ) =
        d ^ (-(5 / 8 : ℝ)) * d ^ (19 / 8 : ℝ) := by
    calc
      _ = d ^ ((-(5 / 8 : ℝ)) + (19 / 8 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hd _ _
  change ell ^ (5 / 2 : ℝ) * d ^ (7 / 4 : ℝ) /
      q ^ 3 ≤ ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))
  apply (div_le_iff₀ (pow_pos hq 3)).2
  calc
    ell ^ (5 / 2 : ℝ) * d ^ (7 / 4 : ℝ) =
        (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) *
          (ell ^ (19 / 8 : ℝ) * d ^ (19 / 8 : ℝ)) := by
      rw [hEllPow,hRadiusPow]
      ring
    _ ≤ (ell ^ (1 / 8 : ℝ) * d ^ (-(5 / 8 : ℝ))) * q ^ 3 :=
      mul_le_mul_of_nonneg_left hScaledPow (by positivity)
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
