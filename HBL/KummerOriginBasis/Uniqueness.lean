import HBL.KummerOriginBasis.Definitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped NNReal
namespace HBL.Profile.Kummer

/-- The origin data determine both regularized solutions uniquely on the full interval. -/
theorem origin_kummer_pair_unique {mu theta R : ℝ}
    (K J : OriginKummerPair mu theta R) :
    ∀ r ∈ Icc 0 R,
      K.y r = J.y r ∧ K.dy r = J.dy r ∧ K.x r = J.x r ∧ K.dx r = J.dx r := by
  let T : ℝ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun r =>
    (ContinuousLinearMap.snd ℂ ℂ ℂ).prod 0 -
      (originFirstCoeff r • (ContinuousLinearMap.prod (0 : (ℂ × ℂ) →L[ℂ] ℂ)
        (ContinuousLinearMap.snd ℂ ℂ ℂ)) +
      originZeroCoeff mu theta • (ContinuousLinearMap.prod (0 : (ℂ × ℂ) →L[ℂ] ℂ)
        (ContinuousLinearMap.fst ℂ ℂ ℂ)))
  have hT : Continuous T := by
    dsimp [T, originFirstCoeff]
    fun_prop
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hT.continuousOn
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  have hlip (r : ℝ) (hr : r ∈ Ico 0 R) :
      LipschitzOnWith C (fun v : ℂ × ℂ => T r v) univ := by
    apply LipschitzWith.lipschitzOnWith
    exact (T r).lipschitzWith.weaken (by
      exact_mod_cast (hC₀ r ⟨hr.1, hr.2.le⟩).trans (le_max_left C₀ 0))
  have hu (u v p q : ℝ → ℂ)
      (hf : ∀ r ∈ Icc 0 R, HasDerivWithinAt (fun t => (u t, v t))
        (T r (u r, v r)) (Icc 0 R) r)
      (hg : ∀ r ∈ Icc 0 R, HasDerivWithinAt (fun t => (p t, q t))
        (T r (p r, q r)) (Icc 0 R) r)
      (hzero : (u 0, v 0) = (p 0, q 0)) :
      EqOn (fun r => (u r, v r)) (fun r => (p r, q r)) (Icc 0 R) := by
    exact ODE_solution_unique_of_mem_Icc_right hlip
      (HasDerivWithinAt.continuousOn hf)
      (fun r hr => (hf r ⟨hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hr.2) (Icc_subset_Icc_left hr.1)))
      (fun _ _ => mem_univ _)
      (HasDerivWithinAt.continuousOn hg)
      (fun r hr => (hg r ⟨hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hr.2) (Icc_subset_Icc_left hr.1)))
      (fun _ _ => mem_univ _) hzero
  have hy := hu K.y K.dy J.y J.dy
    (fun r hr => by simpa [T] using! (K.y_deriv r hr).prodMk (K.dy_deriv r hr))
    (fun r hr => by simpa [T] using! (J.y_deriv r hr).prodMk (J.dy_deriv r hr))
    (by simp [K.y_zero, K.dy_zero, J.y_zero, J.dy_zero])
  have hx := hu K.x K.dx J.x J.dx
    (fun r hr => by simpa [T] using! (K.x_deriv r hr).prodMk (K.dx_deriv r hr))
    (fun r hr => by simpa [T] using! (J.x_deriv r hr).prodMk (J.dx_deriv r hr))
    (by simp [K.x_zero, K.dx_zero, J.x_zero, J.dx_zero])
  intro r hr
  exact ⟨congrArg Prod.fst (hy hr), congrArg Prod.snd (hy hr),
    congrArg Prod.fst (hx hr), congrArg Prod.snd (hx hr)⟩
end HBL.Profile.Kummer
