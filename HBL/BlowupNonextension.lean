import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Strong non-extension from scale separation

This is an unnumbered generic lemma for the final HBL reconstruction.
If a trajectory approaches a fixed background plus a family of profiles
which remains uniformly separated along arbitrarily late pairs, then the
trajectory cannot have a strong limit.  The HBL application uses the
standard scale separation of the energy-critical bubble family.
-/

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace HBL.MainBackward

theorem no_strong_limit_of_separated_profile
    {X : Type*} [NormedAddCommGroup X]
    (u bubble : ℕ → X) (background : X)
    (happrox : Tendsto
      (fun n => dist (u n) (bubble n + background)) atTop (𝓝 0))
    (hsep : ∃ eps : ℝ, 0 < eps ∧
      ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N, eps ≤ dist (bubble m) (bubble n)) :
    ∀ limit : X, ¬ Tendsto u atTop (𝓝 limit) := by
  intro limit hlim
  rcases hsep with ⟨eps, heps, hsep⟩
  let d : ℝ := eps / 8
  have hd : 0 < d := by
    dsimp [d]
    linarith
  rcases Metric.tendsto_atTop.1 hlim d hd with ⟨N1, hN1⟩
  rcases Metric.tendsto_atTop.1 happrox d hd with ⟨N2, hN2⟩
  let N := max N1 N2
  rcases hsep N with ⟨m, hmN, n, hnN, hmn⟩
  have hm1 : N1 ≤ m := le_trans (le_max_left _ _) hmN
  have hm2 : N2 ≤ m := le_trans (le_max_right _ _) hmN
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hnN
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hnN
  have hum : dist (u m) limit < d := hN1 m hm1
  have hun : dist (u n) limit < d := hN1 n hn1
  have hem : dist (u m) (bubble m + background) < d := by
    have h := hN2 m hm2
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using h
  have hen : dist (u n) (bubble n + background) < d := by
    have h := hN2 n hn2
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using h
  have htri1 := dist_triangle (bubble m + background) (u m)
    (bubble n + background)
  have htri2 := dist_triangle (u m) limit (bubble n + background)
  have htri3 := dist_triangle limit (u n) (bubble n + background)
  have htranslate :
      dist (bubble m + background) (bubble n + background) =
        dist (bubble m) (bubble n) := by
    simpa only [dist_eq_norm] using
      congrArg norm (sub_add_sub_cancel (bubble m) (bubble n) background)
  rw [htranslate] at htri1
  have hln : dist limit (u n) = dist (u n) limit := dist_comm _ _
  rw [hln] at htri3
  have hbm : dist (bubble m + background) (u m) =
      dist (u m) (bubble m + background) := dist_comm _ _
  rw [hbm] at htri1
  nlinarith [htri1, htri2, htri3]

#print axioms no_strong_limit_of_separated_profile

end HBL.MainBackward
