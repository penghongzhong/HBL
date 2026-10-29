import HBL.KummerPrescribedAnnulus.ActualPair
import HBL.KummerPrescribedAnnulus.UniformPair

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- A prescribed positive annulus and one bound for every parameter in an
arbitrary compact set. No radius is chosen after the parameter set. -/
theorem exists_compact_prescribed_kummer_pair
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) (z eps : ℝ)
    (heps : 0 < eps) (hz : eps < z) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ A,
      ∃ K : LocalKummerPair p.1 p.2 z eps, LocalKummerBound K C := by
  have hc : ContinuousOn (fun t => frozenFirstCoeff (z + t)) (Icc (-eps) eps) := by
    unfold frozenFirstCoeff
    fun_prop (disch := intro t ht; first | (solve | norm_num) |
      exact_mod_cast (show z + t ≠ 0 by linarith [ht.1]))
  have hp : Continuous (fun p : ℝ × ℝ => frozenZeroCoeff p.1 p.2) := by
    unfold frozenZeroCoeff
    fun_prop
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨M₀, hM₀⟩ := hA.exists_bound_of_continuousOn hp.continuousOn
  let D := max B₀ 0 + max M₀ 0
  have hD : 0 ≤ D := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.exp ((D + 1) * eps), Real.exp_pos _, ?_⟩
  intro p hpA
  obtain ⟨_, _, K, _⟩ := exists_prescribed_bounded_kummer_pair p.1 p.2 z eps heps hz
  refine ⟨K, prescribed_kummer_pair_exp_bound K D hD ?_⟩
  intro t ht
  exact add_le_add ((hB₀ t ht).trans (le_max_left _ _))
    ((hM₀ p hpA).trans (le_max_left _ _))
end HBL.Profile.Kummer
