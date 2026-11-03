import HBL.TypeIIDynamicSelection.ActualHartreeComplexCubicLipschitz
import Mathlib.Tactic

/-!
# Revised HBL 2.13: norm of the exact FOUR-product Hartree interaction

For the original complex cubic factor C(u)=|u|²u, and original
physical core, pure radiation, mixed Hartree Riesz potentials
P_c, P_z, P_m, bound the complete four-product interaction by
its ten explicit nonnegative monomials.

This is an exact deterministic algebraic inequality in the same
three potentials, not a surrogate for their genuine Riesz integrals.
The physical source identification is strictly accepted separately.
-/

noncomputable section
set_option autoImplicit false
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- The full cubic multiplier retained by the actual Hartree
inverse-square quartic nonlocal PDE yields its ten-monomial
upper bound, without treating any interaction as zero. -/
theorem actual_Hartree_four_product_complete_cubic_norm_le
    (v z : ℂ) (pm pz pc : ℝ) :
    ‖(pm : ℂ) * actualHartreeComplexCubic v +
        (pm : ℂ) * (actualHartreeComplexCubic (v + z) -
          actualHartreeComplexCubic v) +
        (pz : ℂ) * (actualHartreeComplexCubic (v + z) -
          actualHartreeComplexCubic z) +
        (pc : ℂ) * (actualHartreeComplexCubic (v + z) -
          actualHartreeComplexCubic v)‖ ≤
      |pm| * (‖v‖ ^ 3 + (2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) +
      |pz| * ((‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖) +
      |pc| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) := by
  let c : ℂ → ℂ := actualHartreeComplexCubic
  let x1 : ℂ := (pm : ℂ) * c v
  let x2 : ℂ := (pm : ℂ) * (c (v + z) - c v)
  let x3 : ℂ := (pz : ℂ) * (c (v + z) - c z)
  let x4 : ℂ := (pc : ℂ) * (c (v + z) - c v)
  have hCore : ‖c v‖ = ‖v‖ ^ 3 := by
    dsimp [c,actualHartreeComplexCubic]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (‖v‖))]
    ring
  have hNorm : ‖v + z‖ ≤ ‖v‖ + ‖z‖ := norm_add_le v z
  have hAddCore :
      ‖v + z‖ + ‖v‖ ≤ 2 * ‖v‖ + ‖z‖ := by
    linarith
  have hAddRad :
      ‖v + z‖ + ‖z‖ ≤ ‖v‖ + 2 * ‖z‖ := by
    linarith
  have hCoreDiff :
      ‖c (v + z) - c v‖ ≤
        (2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖ := by
    have hLip := actual_Hartree_complex_cubic_Lipschitz (v + z) v
    change ‖c (v + z) - c v‖ ≤
      (‖v + z‖ + ‖v‖) ^ 2 * ‖v + z - v‖ at hLip
    calc
      ‖c (v + z) - c v‖ ≤
          (‖v + z‖ + ‖v‖) ^ 2 * ‖v + z - v‖ := hLip
      _ = (‖v + z‖ + ‖v‖) ^ 2 * ‖z‖ := by
        rw [add_sub_cancel_left]
      _ ≤ (2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hAddCore 2)
          (norm_nonneg z)
  have hRadDiff :
      ‖c (v + z) - c z‖ ≤
        (‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖ := by
    have hLip := actual_Hartree_complex_cubic_Lipschitz (v + z) z
    change ‖c (v + z) - c z‖ ≤
      (‖v + z‖ + ‖z‖) ^ 2 * ‖v + z - z‖ at hLip
    calc
      ‖c (v + z) - c z‖ ≤
          (‖v + z‖ + ‖z‖) ^ 2 * ‖v + z - z‖ := hLip
      _ = (‖v + z‖ + ‖z‖) ^ 2 * ‖v‖ := by
        rw [add_sub_cancel_right]
      _ ≤ (‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hAddRad 2)
          (norm_nonneg v)
  have hNorm1 : ‖x1‖ = |pm| * ‖c v‖ := by
    dsimp [x1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hNorm2 : ‖x2‖ = |pm| * ‖c (v + z) - c v‖ := by
    dsimp [x2]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hNorm3 : ‖x3‖ = |pz| * ‖c (v + z) - c z‖ := by
    dsimp [x3]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hNorm4 : ‖x4‖ = |pc| * ‖c (v + z) - c v‖ := by
    dsimp [x4]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 :
      ‖x1‖ = |pm| * ‖v‖ ^ 3 := by rw [hNorm1,hCore]
  have h2 :
      ‖x2‖ ≤ |pm| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) := by
    rw [hNorm2]
    exact mul_le_mul_of_nonneg_left hCoreDiff (abs_nonneg pm)
  have h3 :
      ‖x3‖ ≤ |pz| * ((‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖) := by
    rw [hNorm3]
    exact mul_le_mul_of_nonneg_left hRadDiff (abs_nonneg pz)
  have h4 :
      ‖x4‖ ≤ |pc| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) := by
    rw [hNorm4]
    exact mul_le_mul_of_nonneg_left hCoreDiff (abs_nonneg pc)
  change ‖x1 + x2 + x3 + x4‖ ≤
    |pm| * (‖v‖ ^ 3 + (2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) +
    |pz| * ((‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖) +
    |pc| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖)
  calc
    ‖x1 + x2 + x3 + x4‖ ≤
        ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ := by
      have hab := norm_add_le x1 x2
      have habc := norm_add_le (x1 + x2) x3
      have habcd := norm_add_le (x1 + x2 + x3) x4
      linarith
    _ ≤ |pm| * ‖v‖ ^ 3 +
        |pm| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) +
        |pz| * ((‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖) +
        |pc| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) := by
      rw [h1]
      linarith
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
