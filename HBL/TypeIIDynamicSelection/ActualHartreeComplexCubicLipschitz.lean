import HBL.TypeIIDynamicSelection.ActualWholeRadiationSelfCubic
import Mathlib.Tactic

/-!
# Actual Hartree complex local-cubic two-channel Lipschitz bound

Instead of a seven-term explicit expansion, use the universal cubic
norm difference estimate for C(u)=|u|^2 u and the reverse triangle
inequality. The estimate is entirely algebraic and valid for complex
radiation, real moving-monopole background, and arbitrary phase.

This supplies the exact changed local cubic multiplier entering the
FULL nonlocal Hartree interaction; it is NOT a replacement for the
Riesz potential or its required spatial gain. No Type-II rate,
local cubic substitute for the equation, or axiom is introduced.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original cubic multiplier in the inverse-square Hartree
nonlinearity, separate from its genuine nonlocal potential. -/
def actualHartreeComplexCubic (u : ℂ) : ℂ :=
  (‖u‖ ^ 2 : ℝ) * u

/-- Universal quadratic-coefficient Lipschitz estimate for the
actual complex Hartree cubic. It avoids splitting real and
imaginary channels or assigning independently tuned cubic sources. -/
theorem actual_Hartree_complex_cubic_Lipschitz
    (u v : ℂ) :
    ‖actualHartreeComplexCubic u - actualHartreeComplexCubic v‖ ≤
      (‖u‖ + ‖v‖) ^ 2 * ‖u - v‖ := by
  have hId :
      actualHartreeComplexCubic u - actualHartreeComplexCubic v =
        (((‖u‖ ^ 2 - ‖v‖ ^ 2 : ℝ) : ℂ) * u) +
        ((‖v‖ ^ 2 : ℝ) : ℂ) * (u - v) := by
    unfold actualHartreeComplexCubic
    push_cast
    ring
  have hDiff : |‖u‖ - ‖v‖| ≤ ‖u - v‖ :=
    abs_norm_sub_norm_le u v
  have hNorm : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤
      (‖u‖ + ‖v‖) * ‖u - v‖ := by
    calc
      |‖u‖ ^ 2 - ‖v‖ ^ 2| =
          |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
        rw [show ‖u‖ ^ 2 - ‖v‖ ^ 2 =
          (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) by ring,
          abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      _ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
        mul_le_mul_of_nonneg_right hDiff
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  rw [hId]
  calc
    ‖(((‖u‖ ^ 2 - ‖v‖ ^ 2 : ℝ) : ℂ) * u) +
        ((‖v‖ ^ 2 : ℝ) : ℂ) * (u - v)‖ ≤
      ‖(((‖u‖ ^ 2 - ‖v‖ ^ 2 : ℝ) : ℂ) * u)‖ +
        ‖((‖v‖ ^ 2 : ℝ) : ℂ) * (u - v)‖ :=
      norm_add_le _ _
    _ = |‖u‖ ^ 2 - ‖v‖ ^ 2| * ‖u‖ +
        ‖v‖ ^ 2 * ‖u - v‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (‖v‖))]
    _ ≤ ((‖u‖ + ‖v‖) * ‖u - v‖) * ‖u‖ +
        ‖v‖ ^ 2 * ‖u - v‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hNorm (norm_nonneg u)) le_rfl
    _ ≤ (‖u‖ + ‖v‖) ^ 2 * ‖u - v‖ := by
      have hUV : 0 ≤ ‖u‖ * ‖v‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hUVW : 0 ≤ (‖u‖ * ‖v‖) * ‖u - v‖ :=
        mul_nonneg hUV (norm_nonneg _)
      nlinarith only [hUVW]

/-- The exact full-minus-core Hartree cubic difference is
linear in the radiation amplitude with its true quadratic weight. -/
theorem actual_Hartree_cubic_full_minus_core_bound
    (v : ℝ) (z : ℂ) :
    ‖actualHartreeComplexCubic ((v : ℂ) + z) -
        actualHartreeComplexCubic (v : ℂ)‖ ≤
      (‖(v : ℂ) + z‖ + |v|) ^ 2 * ‖z‖ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    add_sub_cancel_left] using
    (actual_Hartree_complex_cubic_Lipschitz ((v : ℂ) + z) (v : ℂ))

/-- The exact full-minus-radiation Hartree cubic difference is
linear in the genuine core amplitude, not a guessed source. -/
theorem actual_Hartree_cubic_full_minus_radiation_bound
    (v : ℝ) (z : ℂ) :
    ‖actualHartreeComplexCubic ((v : ℂ) + z) -
        actualHartreeComplexCubic z‖ ≤
      (‖(v : ℂ) + z‖ + ‖z‖) ^ 2 * |v| := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    add_sub_cancel_right] using
    (actual_Hartree_complex_cubic_Lipschitz ((v : ℂ) + z) z)

/-- Identifies the cubic factor with the existing exact PDE source
for an arbitrary complex radial physical radiation field. -/
theorem actual_Hartree_complex_cubic_is_same_PDE_factor
    (u : ℝ → ℂ) (r : ℝ) :
    actualWholeRadiationLocalCubic u r =
      actualHartreeComplexCubic (u r) := rfl

end HBL.TypeIIDynamicSelection
