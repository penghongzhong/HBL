import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem exists_common_kummer_radius (eps C M : ℝ) (heps : 0 < eps) (hC : 0 < C) (hM : 0 ≤ M) :
    ∃ d B : ℝ, 0 < d ∧ d < eps ∧ 0 < B ∧ B = 4 * d * C ^ 3 ∧ (M + 1) * B ≤ (1 / 4 : ℝ) := by
  let d := min (eps / 2) (1 / (16 * C ^ 3 * (M + 1)))
  have hden : 0 < 16 * C ^ 3 * (M + 1) := by positivity
  have hd : 0 < d := lt_min (half_pos heps) (one_div_pos.mpr hden)
  have hde : d < eps := (min_le_left _ _).trans_lt (by linarith)
  have hsmall : d * (16 * C ^ 3 * (M + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨d,4 * d * C ^ 3,hd,hde,by positivity,rfl,?_⟩
  nlinarith
end HBL.Profile.Kummer
