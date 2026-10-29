import HBL.KummerPrescribedAnnulus.Clip

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped NNReal
namespace HBL.Profile.Kummer

/-- Linear ODEs with continuous bounded coefficients exist on a prescribed
finite interval. No smallness restriction is imposed on its length. -/
theorem exists_linear_ivp_on_prescribed_interval
    (n : ℕ) (a b : ℝ) (hab : a ≤ b)
    (A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hA : ContinuousOn A (Icc a b)) (C : ℝ≥0)
    (hC : ∀ t ∈ Icc a b, ‖A t‖ ≤ C) (x₀ : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, x a = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt x (A t (x t)) (Icc a b) t := by
  obtain ⟨hclipLip, hclipBound, hclipNorm, hclipId⟩ := clipRealVector_properties n
  let δ : ℝ := (Real.exp ((C : ℝ) * (b - a)) * (1 + ‖x₀‖))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let y₀ := δ • x₀
  let r : ℝ≥0 := ‖y₀‖₊
  let R : ℝ≥0 := C * ⟨b - a, sub_nonneg.mpr hab⟩ + r
  let f : ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun t x => A t (clipRealVector x)
  have hf : IsPicardLindelof f (⟨a, ⟨le_rfl, hab⟩⟩ : Icc a b)
      0 R r C C := {
    lipschitzOnWith := by
      intro t ht
      exact (((A t).lipschitzWith.weaken (by exact_mod_cast hC t ht)).comp
        hclipLip |>.weaken (by simp)).lipschitzOnWith
    continuousOn := by
      intro x _
      exact hA.clm_apply continuousOn_const
    norm_le := by
      intro t ht x _
      calc
        ‖f t x‖ ≤ ‖A t‖ * ‖clipRealVector x‖ := (A t).le_opNorm _
        _ ≤ (C : ℝ) * 1 := mul_le_mul (hC t ht) (hclipBound x)
          (norm_nonneg _) C.coe_nonneg
        _ = C := mul_one _
    mul_max_le := by
      simp only [sub_self, max_eq_left (sub_nonneg.mpr hab)]
      simp only [R, NNReal.coe_add, NNReal.coe_mul, add_sub_cancel_right]
      exact le_rfl }
  obtain ⟨y, hy₀, hy⟩ := hf.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (show y₀ ∈ closedBall (0 : Fin n → ℝ) r by simp [r])
  have hyCont : ContinuousOn y (Icc a b) := HasDerivWithinAt.continuousOn hy
  have hgrowth : ∀ t ∈ Icc a b, ‖y t‖ ≤ ‖y₀‖ * Real.exp ((C : ℝ) * (t - a)) := by
    intro t ht
    have hh := norm_le_gronwallBound_of_norm_deriv_right_le hyCont
      (fun s hs => (hy s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
      (show ‖y a‖ ≤ ‖y₀‖ by rw [hy₀])
      (fun s hs => show ‖f s (y s)‖ ≤ (C : ℝ) * ‖y s‖ + 0 from by
        simpa using ((A s).le_opNorm (clipRealVector (y s))).trans
          (mul_le_mul (hC s ⟨hs.1, hs.2.le⟩) (hclipNorm (y s))
            (norm_nonneg _) C.coe_nonneg)) t ht
    simpa only [gronwallBound_ε0] using hh
  have hunit : ∀ t ∈ Icc a b, ‖y t‖ ≤ 1 := by
    intro t ht
    calc
      ‖y t‖ ≤ ‖y₀‖ * Real.exp ((C : ℝ) * (t - a)) := hgrowth t ht
      _ ≤ ‖y₀‖ * Real.exp ((C : ℝ) * (b - a)) := by gcongr; exact ht.2
      _ ≤ 1 := by
        rw [show ‖y₀‖ = δ * ‖x₀‖ by simp [y₀, norm_smul, abs_of_pos hδ]]
        dsimp [δ]
        have he := Real.exp_pos ((C : ℝ) * (b - a))
        have hn : 0 < 1 + ‖x₀‖ := by positivity
        apply (mul_le_mul_iff_right₀ (mul_pos he hn)).mp
        field_simp
        nlinarith
  refine ⟨fun t => δ⁻¹ • y t, ?_, ?_⟩
  · change δ⁻¹ • y a = x₀
    change y a = y₀ at hy₀
    rw [hy₀]
    simp [y₀, smul_smul, hδ.ne']
  · intro t ht
    have hh := (hy t ht).const_smul δ⁻¹
    simpa only [f, hclipId (y t) (hunit t ht), map_smul] using! hh
end HBL.Profile.Kummer
