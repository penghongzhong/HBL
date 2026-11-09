import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import Mathlib.Tactic

/-!
# Exact original complex Hartree cubic Taylor under the half-radial weight

The real two-scale Hartree radiation only yields (1+r)|U|^2<=K,
not |U|<=M*bubble. The actual cubic factors of the FULL
nonlocal seventh-degree Taylor expansion then have precisely:
 (1+r)^3*|C(U)|^2 <= K^3,
 (1+r)^2*|DC(U)[H]| <= 6Ke,
 (1+r)^2*|C_{>=2}(U,H)| <= 4(3M+e)e^2,
whenever (1+r)|H|<=2e and |U|<=M, |H|<=e.
These are derived from the original cubic |U|^2 U, not an
abstract independent source. No time rate or PDE orbit is assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_Hartree_half_radial_original_cubic_Taylor_weighted
    (u h : ℂ) (t M K e : ℝ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hu : ‖u‖ ≤ M)
    (hHalf : t*‖u‖^2 ≤ K)
    (hh : ‖h‖ ≤ e)
    (hHweight : t*‖h‖ ≤ 2*e) :
    t^3*‖actualHartreeComplexCubic u‖^2 ≤ K^3 ∧
    t^2*‖actualHartreeComplexCubicLinear u h‖ ≤ 6*K*e ∧
    t^2*‖actualHartreeComplexCubicRemainder u h‖ ≤
      4*(3*M+e)*e^2 := by
  have ht0 : 0 ≤ t := by linarith
  have hPoly :=
    actual_Hartree_complex_Taylor_polynomial_bounds
      u h (norm_nonneg u) (norm_nonneg h) le_rfl le_rfl
  have hCubic : ‖actualHartreeComplexCubic u‖ = ‖u‖^3 := by
    unfold actualHartreeComplexCubic
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖u‖)]
    ring
  have hC0 :
      t^3*‖actualHartreeComplexCubic u‖^2 ≤ K^3 := by
    calc
      _ = (t*‖u‖^2)^3 := by rw [hCubic]; ring
      _ ≤ K^3 :=
        pow_le_pow_left₀ (mul_nonneg ht0 (sq_nonneg _)) hHalf 3
  have hC1raw :
      ‖actualHartreeComplexCubicLinear u h‖ ≤
        3*‖u‖^2*‖h‖ := hPoly.2.2.2.1
  have hProd :
      (t*‖u‖^2)*(t*‖h‖) ≤ K*(2*e) :=
    mul_le_mul hHalf hHweight (by positivity) hK
  have hC1 :
      t^2*‖actualHartreeComplexCubicLinear u h‖ ≤ 6*K*e := by
    calc
      _ ≤ t^2*(3*‖u‖^2*‖h‖) :=
        mul_le_mul_of_nonneg_left hC1raw (sq_nonneg _)
      _ = 3*((t*‖u‖^2)*(t*‖h‖)) := by ring
      _ ≤ 3*(K*(2*e)) :=
        mul_le_mul_of_nonneg_left hProd (by norm_num)
      _ = 6*K*e := by ring
  have hCRraw :
      ‖actualHartreeComplexCubicRemainder u h‖ ≤
        (3*‖u‖+‖h‖)*‖h‖^2 := hPoly.2.2.2.2
  have hCoef : 3*‖u‖+‖h‖ ≤ 3*M+e := by linarith
  have hHsq :
      t^2*‖h‖^2 ≤ (2*e)^2 := by
    have hp := pow_le_pow_left₀
      (mul_nonneg ht0 (norm_nonneg h)) hHweight 2
    simpa only [mul_pow] using hp
  have hCR :
      t^2*‖actualHartreeComplexCubicRemainder u h‖ ≤
        4*(3*M+e)*e^2 := by
    calc
      _ ≤ t^2*((3*‖u‖+‖h‖)*‖h‖^2) :=
        mul_le_mul_of_nonneg_left hCRraw (sq_nonneg _)
      _ = (3*‖u‖+‖h‖)*(t^2*‖h‖^2) := by ring
      _ ≤ (3*M+e)*(2*e)^2 :=
        mul_le_mul hCoef hHsq (by positivity) (by positivity)
      _ = 4*(3*M+e)*e^2 := by ring
  exact ⟨hC0,hC1,hCR⟩

end HBL.TypeIIDynamicSelection
