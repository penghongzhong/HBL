import HBL.KummerPrescribedAnnulus.PhysicalDefinitions

noncomputable section
set_option autoImplicit false
open Set
open scoped NNReal
namespace HBL.Profile.Kummer

/-- A nonzero initial determinant stays nonzero throughout the prescribed
positive interval, including its endpoints. -/
theorem kummer_wronskian_ne_on_prescribed_interval
    (mu theta a b : ℝ) (ha : 0 < a)
    (u v p q : ℝ → ℂ)
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (v t) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v
      (-(frozenFirstCoeff t * v t + frozenZeroCoeff mu theta * u t)) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (q t) (Icc a b) t)
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q
      (-(frozenFirstCoeff t * q t + frozenZeroCoeff mu theta * p t)) (Icc a b) t)
    (h₀ : u a * q a - v a * p a ≠ 0) :
    ∀ t ∈ Icc a b, u t * q t - v t * p t ≠ 0 := by
  let W := fun t => u t * q t - v t * p t
  have hW : ∀ t ∈ Icc a b,
      HasDerivWithinAt W (-frozenFirstCoeff t * W t) (Icc a b) t := by
    intro t ht
    convert ((hu t ht).mul (hq t ht)).sub ((hv t ht).mul (hp t ht)) using 1
    dsimp [W]
    ring
  have hc : ContinuousOn frozenFirstCoeff (Icc a b) := by
    unfold frozenFirstCoeff
    fun_prop (disch := intro t ht; first | (solve | norm_num) |
      exact_mod_cast ne_of_gt (ha.trans_le ht.1))
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  intro t ht hzero
  have hsubset : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hlip : ∀ s ∈ Ioc a t,
      LipschitzOnWith C (fun w : ℂ => -frozenFirstCoeff s * w) univ := by
    intro s hs
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, ← mul_sub, norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_right
      ((hC₀ s ⟨hs.1.le, hs.2.trans ht.2⟩).trans (le_max_left _ _)) (norm_nonneg _)
  have heq : EqOn W (fun _ => (0 : ℂ)) (Icc a t) :=
    ODE_solution_unique_of_mem_Icc_left hlip
      ((HasDerivWithinAt.continuousOn hW).mono hsubset)
      (fun s hs => (hW s ⟨hs.1.le, hs.2.trans ht.2⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsLE hs.1)
          (Icc_subset_Icc_right (hs.2.trans ht.2))))
      (fun _ _ => mem_univ _) continuousOn_const
      (fun s _ => by simpa using (hasDerivAt_const s (0 : ℂ)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hzero
  exact h₀ (heq ⟨le_rfl, ht.1⟩)
end HBL.Profile.Kummer
