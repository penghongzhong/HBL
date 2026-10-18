import HBL.MonopoleCutoffEquation

/-! A concrete amplitude-dependent radius and the actual quadratic core defect. -/

noncomputable section

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail

/-- The chosen global cutoff radius for a nonzero small amplitude. -/
def monopoleQuadraticRadius (c : ℝ) : ℝ := 4 / |c|

/-- The chosen radius is in the range of the actual tail estimate. -/
theorem monopoleQuadraticRadius_ge_four {c : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) :
    4 ≤ monopoleQuadraticRadius c := by
  unfold monopoleQuadraticRadius
  exact (le_div_iff₀ hc).2 (by linarith)

/-- The genuine cutoff contribution has a uniform quadratic amplitude bound. -/
theorem monopoleQuadraticRadius_core_defect {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r)
    (hsep : r ≤ monopoleQuadraticRadius c / 2) :
    |c * (hPlusApply (monopoleInnerProfile (monopoleQuadraticRadius c)) r -
      monopoleSource r) / r| ≤
      Real.pi * hartreeKappa * monopoleLinearGrowthConstant * c ^ 2 * bubble r ^ 3 := by
  have hR := monopoleQuadraticRadius_ge_four hc hc1
  have hb := monopoleInnerProfile_hPlus_core_abs_le hR hr hsep
  have hc0 : |c| ≠ 0 := ne_of_gt hc
  have hcube : |c| ^ 3 ≤ c ^ 2 := by
    nlinarith [sq_nonneg (|c|), sq_abs c]
  have hnonneg : 0 ≤ Real.pi * hartreeKappa * monopoleLinearGrowthConstant *
      bubble r ^ 3 := by
    have hM := monopoleLinearGrowthConstant_pos
    unfold hartreeKappa bubble
    positivity
  rw [abs_div, abs_mul, abs_of_pos hr]
  calc
    |c| * |hPlusApply (monopoleInnerProfile (monopoleQuadraticRadius c)) r -
        monopoleSource r| / r ≤
        |c| * (16 * Real.pi * hartreeKappa * monopoleLinearGrowthConstant *
          r * bubble r ^ 3 / (monopoleQuadraticRadius c) ^ 2) / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hc.le) hr.le
    _ = (Real.pi * hartreeKappa * monopoleLinearGrowthConstant * bubble r ^ 3) *
        |c| ^ 3 := by
      unfold monopoleQuadraticRadius
      field_simp
      ring
    _ ≤ (Real.pi * hartreeKappa * monopoleLinearGrowthConstant * bubble r ^ 3) *
        c ^ 2 := mul_le_mul_of_nonneg_left hcube hnonneg
    _ = _ := by ring

end HBL.Modulation.Monopole
