import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem compact_parameters_abs_bound (A : Set (ℝ × ℝ)) (hA : IsCompact A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ A, |p.1| + |p.2| ≤ M := by
  obtain ⟨R,hR⟩ := hA.isBounded.exists_norm_le
  refine ⟨max (2 * R) 0, le_max_right _ _, ?_⟩
  intro p hp
  have h := hR p hp
  simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] at h
  have hm := le_max_left (2 * R) 0
  linarith
end HBL.Profile.Kummer
