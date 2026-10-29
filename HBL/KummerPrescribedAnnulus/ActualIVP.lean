import HBL.KummerPrescribedAnnulus.PhysicalDefinitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped NNReal
namespace HBL.Profile.Kummer

/-- The actual frozen Kummer IVP on any prescribed positive finite interval. -/
theorem exists_actual_kummer_prescribed_ivp
    (mu theta a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (u₀ v₀ : ℂ) :
    ∃ u v : ℝ → ℂ, u a = u₀ ∧ v a = v₀ ∧
      ∀ t ∈ Icc a b,
        HasDerivWithinAt u (v t) (Icc a b) t ∧
        HasDerivWithinAt v
          (-(frozenFirstCoeff t * v t + frozenZeroCoeff mu theta * u t))
          (Icc a b) t := by
  have hA : ContinuousOn (realKummerOperator mu theta) (Icc a b) := by
    have hi : ContinuousOn (fun t : ℝ => 2 / t) (Icc a b) :=
      continuousOn_const.div₀ continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
    have hh : Continuous (fun t : ℝ => t / 2) := by fun_prop
    unfold realKummerOperator
    exact (continuousOn_const.sub (hi.smul continuousOn_const)).add
      (hh.continuousOn.smul continuousOn_const)
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  obtain ⟨x, hx₀, hx⟩ := exists_linear_ivp_on_prescribed_interval 4 a b hab
    (realKummerOperator mu theta) hA C
    (fun t ht => (hC₀ t ht).trans (le_max_left _ _)) (encodeKummerJet u₀ v₀)
  refine ⟨fun t => realJetValue (x t), fun t => realJetSlope (x t), ?_, ?_, ?_⟩
  · change realJetValue (x a) = u₀
    rw [hx₀]
    simpa [realJetValue, encodeKummerJet, mul_comm] using u₀.re_add_im
  · change realJetSlope (x a) = v₀
    rw [hx₀]
    simpa [realJetSlope, encodeKummerJet, mul_comm] using v₀.re_add_im
  · intro t ht
    have hu := realJetValue.hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
    have hv := realJetSlope.hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
    have heq₁ : realJetValue (realKummerOperator mu theta t (x t)) =
        realJetSlope (x t) := by
      simp [realJetValue, realJetSlope, realKummerOperator, realJetEntry]
    have heq₂ : realJetSlope (realKummerOperator mu theta t (x t)) =
        -(frozenFirstCoeff t * realJetSlope (x t) +
          frozenZeroCoeff mu theta * realJetValue (x t)) := by
      simp [realJetValue, realJetSlope, realKummerOperator, realJetEntry,
        frozenFirstCoeff, frozenZeroCoeff]
      ring_nf
      simp only [Complex.I_sq]
      ring
    exact ⟨by simpa only [heq₁, Function.comp_def] using hu,
      by simpa only [heq₂, Function.comp_def] using hv⟩
end HBL.Profile.Kummer
