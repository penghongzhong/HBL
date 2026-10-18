import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A quantitative scalar inverse on a closed symmetric interval. The hypotheses
are standard continuity and a lower bound for decrease; applications must
prove these properties for their actual scalar function.
-/

noncomputable section

open Set

namespace HBL.Kinematic

theorem scalarInverse_separation {F : ℝ → ℝ} {R m x y : ℝ}
    (hdec : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, x ≤ y →
      m * (y - x) ≤ F x - F y)
    (hx : x ∈ Icc (-R) R) (hy : y ∈ Icc (-R) R) :
    m * |x - y| ≤ |F x - F y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    calc
      m * -(x - y) = m * (y - x) := by ring
      _ ≤ F x - F y := hdec x hx y hy hxy
      _ ≤ |F x - F y| := le_abs_self _
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    calc
      m * (x - y) ≤ F y - F x := hdec y hy x hx hyx
      _ ≤ |F y - F x| := le_abs_self _
      _ = |F x - F y| := abs_sub_comm _ _

theorem scalarInverse_root_bound {F : ℝ → ℝ} {R m κ : ℝ}
    (hR : 0 < R)
    (hdec : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, x ≤ y →
      m * (y - x) ≤ F x - F y)
    (hκ : κ ∈ Icc (-R) R) (hroot : F κ = 0) :
    m * |κ| ≤ |F 0| := by
  have h := scalarInverse_separation hdec hκ
    (by constructor <;> linarith : (0 : ℝ) ∈ Icc (-R) R)
  simpa [hroot] using h

theorem scalarInverse_existsUnique_root {F : ℝ → ℝ} {R m : ℝ}
    (hR : 0 < R) (hm : 0 < m)
    (hc : ContinuousOn F (Icc (-R) R))
    (hdec : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, x ≤ y →
      m * (y - x) ≤ F x - F y)
    (hsmall : |F 0| ≤ m * R) :
    ∃! κ : ℝ, κ ∈ Icc (-R) R ∧ F κ = 0 := by
  have h0 : (0 : ℝ) ∈ Icc (-R) R := by constructor <;> linarith
  have hleft : -R ∈ Icc (-R) R := by constructor <;> linarith
  have hright : R ∈ Icc (-R) R := by constructor <;> linarith
  have hl := hdec (-R) hleft 0 h0 (by linarith)
  have hr := hdec 0 h0 R hright (by linarith)
  have hb := abs_le.mp hsmall
  have hsign : (0 : ℝ) ∈ Icc (F R) (F (-R)) := by
    constructor <;> nlinarith
  obtain ⟨κ, hκ, hroot⟩ := intermediate_value_Icc'
    (by linarith : -R ≤ R) hc hsign
  refine ⟨κ, ⟨hκ, hroot⟩, ?_⟩
  intro η hη
  have hsep := scalarInverse_separation hdec hη.1 hκ
  rw [hη.2, hroot, sub_self, abs_zero] at hsep
  have habs : |η - κ| = 0 := by nlinarith [abs_nonneg (η - κ)]
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

theorem scalarInverse_existsUnique_root_with_bound {F : ℝ → ℝ} {R m : ℝ}
    (hR : 0 < R) (hm : 0 < m)
    (hc : ContinuousOn F (Icc (-R) R))
    (hdec : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, x ≤ y →
      m * (y - x) ≤ F x - F y)
    (hsmall : |F 0| ≤ m * R) :
    ∃ κ : ℝ, κ ∈ Icc (-R) R ∧ F κ = 0 ∧
      m * |κ| ≤ |F 0| ∧
      ∀ η ∈ Icc (-R) R, F η = 0 → η = κ := by
  obtain ⟨κ, hκ, huniq⟩ := scalarInverse_existsUnique_root hR hm hc hdec hsmall
  exact ⟨κ, hκ.1, hκ.2, scalarInverse_root_bound hR hdec hκ.1 hκ.2,
    fun η hη hr => huniq η ⟨hη, hr⟩⟩

theorem scalarInverse_root_stability {F G : ℝ → ℝ} {R m E κ η : ℝ}
    (hdec : ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R, x ≤ y →
      m * (y - x) ≤ F x - F y)
    (hκ : κ ∈ Icc (-R) R) (hη : η ∈ Icc (-R) R)
    (hF : F κ = 0) (hG : G η = 0)
    (hgap : ∀ x ∈ Icc (-R) R, |F x - G x| ≤ E) :
    m * |κ - η| ≤ E := by
  have hsep := scalarInverse_separation hdec hκ hη
  have he := hgap η hη
  simpa [hF, hG] using hsep.trans (by simpa [hF, hG] using he)

end HBL.Kinematic
