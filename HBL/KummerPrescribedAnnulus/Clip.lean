import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

def clipRealVector {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max (-1) (min 1 (x i))

/-- A bounded Lipschitz truncation used only in the existence proof. -/
theorem clipRealVector_properties (n : ℕ) :
    LipschitzWith 1 (@clipRealVector n) ∧
    (∀ x : Fin n → ℝ, ‖clipRealVector x‖ ≤ 1) ∧
    (∀ x : Fin n → ℝ, ‖clipRealVector x‖ ≤ ‖x‖) ∧
    (∀ x : Fin n → ℝ, ‖x‖ ≤ 1 → clipRealVector x = x) := by
  have hl : LipschitzWith 1 (@clipRealVector n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    have hi := (((LipschitzWith.eval i).const_min 1).const_max (-1)).dist_le_mul x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, clipRealVector, Pi.sub_apply] using hi
  have hz : clipRealVector (0 : Fin n → ℝ) = 0 := by
    ext i
    norm_num [clipRealVector]
  refine ⟨hl, ?_, ?_, ?_⟩
  · intro x
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · intro x
    simpa [dist_eq_norm, hz] using hl.dist_le_mul x 0
  · intro x hx
    ext i
    have hi : |x i| ≤ 1 := (norm_le_pi_norm x i).trans hx
    simp only [clipRealVector, min_eq_right (abs_le.mp hi).2,
      max_eq_right (abs_le.mp hi).1]
end HBL.Profile.Kummer
