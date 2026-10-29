import HBL.KummerOriginGreen.GreenTerminal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

/-- Actual source linearity of the origin-normalized outgoing Green coefficients,
rather than an abstract linear regional-solver assumption. -/
theorem originGreen_coefficients_add_smul {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (c : ℂ) {r : ℝ} (hr : r ∈ Icc a b) :
    originGreenCoeffA K b (fun s => F s + c * G s) r =
      originGreenCoeffA K b F r + c * originGreenCoeffA K b G r ∧
    originGreenCoeffB K a (fun s => F s + c * G s) r =
      originGreenCoeffB K a F r + c * originGreenCoeffB K a G r := by
  have hf := originGreen_sources_continuous K hK F hF
  have hg := originGreen_sources_continuous K hK G hG
  have ha : a ∈ Icc a b := ⟨le_refl _, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_refl _⟩
  have hA : originGreenSourceA K (fun s => F s + c * G s) =
      (fun s => originGreenSourceA K F s + c * originGreenSourceA K G s) := by
    funext s
    unfold originGreenSourceA
    ring
  have hB : originGreenSourceB K (fun s => F s + c * G s) =
      (fun s => originGreenSourceB K F s + c * originGreenSourceB K G s) := by
    funext s
    unfold originGreenSourceB
    ring
  constructor
  · unfold originGreenCoeffA
    rw [hA, intervalIntegral.integral_add
      (hf.2.1.mono (uIcc_subset_Icc hr hb)).intervalIntegrable
      ((hg.2.1.mono (uIcc_subset_Icc hr hb)).intervalIntegrable.const_mul c),
      intervalIntegral.integral_const_mul]
  · unfold originGreenCoeffB
    rw [hB, intervalIntegral.integral_add
      (hf.2.2.mono (uIcc_subset_Icc ha hr)).intervalIntegrable
      ((hg.2.2.mono (uIcc_subset_Icc ha hr)).intervalIntegrable.const_mul c),
      intervalIntegral.integral_const_mul]

/-- The two actual Green jets are complex linear in the physical source. -/
theorem originGreen_value_slope_add_smul {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (c : ℂ) {r : ℝ} (hr : r ∈ Icc a b) :
    originGreenValue K a b (fun s => F s + c * G s) r =
      originGreenValue K a b F r + c * originGreenValue K a b G r ∧
    originGreenSlope K a b (fun s => F s + c * G s) r =
      originGreenSlope K a b F r + c * originGreenSlope K a b G r := by
  have hc := originGreen_coefficients_add_smul K hK hab F G hF hG c hr
  constructor
  · unfold originGreenValue
    rw [hc.1, hc.2]
    ring
  · unfold originGreenSlope
    rw [hc.1, hc.2]
    ring

/-- Lipschitz stability of the *actual* physical outgoing Green inverse,
measuring the real radial value and derivative without abstract solver inputs. -/
theorem originGreen_source_difference_bound {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b C M : ℝ)
    (hab : a ≤ b) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ r ∈ Icc a b, ‖F r - G r‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ‖originGreenValue K a b F r - originGreenValue K a b G r‖ +
      ‖originGreenSlope K a b F r - originGreenSlope K a b G r‖ ≤
      (2 * C ^ 3 * (b - a)) * M := by
  have hlin := originGreen_value_slope_add_smul K hK hab F G hF hG (-1) hr
  have hv : originGreenValue K a b (fun s => F s - G s) r =
      originGreenValue K a b F r - originGreenValue K a b G r := by
    simpa only [neg_one_mul, sub_eq_add_neg] using hlin.1
  have hd : originGreenSlope K a b (fun s => F s - G s) r =
      originGreenSlope K a b F r - originGreenSlope K a b G r := by
    simpa only [neg_one_mul, sub_eq_add_neg] using hlin.2
  have hbase := originGreen_value_slope_norm_le K a b C M hC hM hK
    (fun s => F s - G s) hFG hr
  rw [hv, hd] at hbase
  exact hbase

/-- A single source stability constant works on any prescribed positive
annulus, for all parameters in an arbitrary compact real parameter set. -/
theorem exists_compact_originGreen_source_stability
    (A : Set (ℝ × ℝ)) (hA : IsCompact A)
    (a b M : ℝ) (ha : 0 < a) (hab : a < b) (hM : 0 ≤ M)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ r ∈ Icc a b, ‖F r - G r‖ ≤ M) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧ ∀ p ∈ A,
      ∃ K : OriginKummerPair p.1 p.2 (b + 1),
        OriginBasisOn K a b C ∧
        ∀ r ∈ Icc a b,
          ‖originGreenValue K a b F r - originGreenValue K a b G r‖ +
          ‖originGreenSlope K a b F r - originGreenSlope K a b G r‖ ≤
            (2 * C ^ 3 * (b - a)) * M := by
  obtain ⟨C, H, hC, hH, hpairs⟩ :=
    exists_compact_origin_kummer_basis A hA a b ha hab
  refine ⟨C, H, hC, hH, ?_⟩
  intro p hp
  obtain ⟨K, hK, _, _, _⟩ := hpairs p hp
  refine ⟨K, hK, ?_⟩
  intro r hr
  exact originGreen_source_difference_bound K a b C M hab.le hC.le hM
    hK F G hF hG hFG hr

end HBL.Profile.Kummer
