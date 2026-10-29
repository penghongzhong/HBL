import HBL.KummerOriginGreen.GreenBridge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

/-- Actual source bounds in the origin-normalized gauge. -/
theorem originGreen_source_norm_le {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) {r : ℝ} (hr : r ∈ Icc a b) (hF : ‖F r‖ ≤ M) :
    ‖originGreenSourceA K F r‖ ≤ C ^ 2 * M ∧
    ‖originGreenSourceB K F r‖ ≤ C ^ 2 * M := by
  rcases hK r hr with ⟨_, _, _, _, _, _, hphi, _, hpsi, _, hW⟩
  have hbound (p : ℂ) (hp : ‖p‖ ≤ C) :
      ‖p * F r / originGreenWronskian K r‖ ≤ C ^ 2 * M := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      _ ≤ C * M * C := mul_le_mul (mul_le_mul hp hF (norm_nonneg _) hC)
        hW (by positivity) (mul_nonneg hC hM)
      _ = _ := by ring
  exact ⟨hbound _ hpsi, hbound _ hphi⟩

/-- The true integral coefficients grow at most linearly with interval length. -/
theorem originGreen_coefficients_norm_le {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Icc a b, ‖F r‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ‖originGreenCoeffA K b F r‖ ≤ C ^ 2 * M * (b - r) ∧
    ‖originGreenCoeffB K a F r‖ ≤ C ^ 2 * M * (r - a) := by
  have hA : ‖originGreenCoeffA K b F r‖ ≤ C ^ 2 * M * |b - r| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hr.2] at hs
    have hsr : s ∈ Icc a b := ⟨hr.1.trans hs.1.le, hs.2⟩
    exact (originGreen_source_norm_le K hC hM hK F hsr (hF s hsr)).1
  have hB : ‖originGreenCoeffB K a F r‖ ≤ C ^ 2 * M * |r - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hr.1] at hs
    have hsr : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans hr.2⟩
    exact (originGreen_source_norm_le K hC hM hK F hsr (hF s hsr)).2
  simpa only [abs_of_nonneg (sub_nonneg.mpr hr.2),
    abs_of_nonneg (sub_nonneg.mpr hr.1)] using And.intro hA hB

/-- A uniform physical C1 estimate, independent of an abstract solver package. -/
theorem originGreen_value_slope_norm_le {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Icc a b, ‖F r‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ‖originGreenValue K a b F r‖ + ‖originGreenSlope K a b F r‖ ≤
      (2 * C ^ 3 * (b - a)) * M := by
  have hcoef := originGreen_coefficients_norm_le K a b C M hC hM hK F hF hr
  rcases hK r hr with ⟨_, _, _, _, _, _, hphi, hdphi, hpsi, hdpsi, _⟩
  have hbound (p q : ℂ) (hp : ‖p‖ ≤ C) (hq : ‖q‖ ≤ C) :
      ‖p * originGreenCoeffA K b F r + q * originGreenCoeffB K a F r‖ ≤
        C ^ 3 * (b - a) * M := by
    calc
      _ ≤ ‖p‖ * ‖originGreenCoeffA K b F r‖ +
          ‖q‖ * ‖originGreenCoeffB K a F r‖ := by
        simpa only [norm_mul] using norm_add_le
          (p * originGreenCoeffA K b F r) (q * originGreenCoeffB K a F r)
      _ ≤ C * (C ^ 2 * M * (b - r)) + C * (C ^ 2 * M * (r - a)) :=
        _root_.add_le_add (mul_le_mul hp hcoef.1 (norm_nonneg _) hC)
          (mul_le_mul hq hcoef.2 (norm_nonneg _) hC)
      _ = _ := by ring
  have hv := hbound (originPhysicalValue K.y r) (originPhysicalValue K.x r) hphi hpsi
  have hd := hbound (originPhysicalSlope K.y K.dy r)
    (originPhysicalSlope K.x K.dx r) hdphi hdpsi
  change ‖originPhysicalValue K.y r * originGreenCoeffA K b F r +
      originPhysicalValue K.x r * originGreenCoeffB K a F r‖ +
    ‖originPhysicalSlope K.y K.dy r * originGreenCoeffA K b F r +
      originPhysicalSlope K.x K.dx r * originGreenCoeffB K a F r‖ ≤ _
  nlinarith

/-- One uniform constant works for every parameter in a prescribed compact set. -/
theorem exists_compact_originGreen_value_slope_bound
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) (a b M : ℝ)
    (ha : 0 < a) (hab : a < b) (hM : 0 ≤ M)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Icc a b, ‖F r‖ ≤ M) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧ ∀ p ∈ A,
      ∃ K : OriginKummerPair p.1 p.2 (b + 1),
        OriginBasisOn K a b C ∧
        ∀ r ∈ Icc a b,
          ‖originGreenValue K a b F r‖ + ‖originGreenSlope K a b F r‖ ≤
            (2 * C ^ 3 * (b - a)) * M := by
  obtain ⟨C, H, hC, hH, hpairs⟩ :=
    exists_compact_origin_kummer_basis A hA a b ha hab
  refine ⟨C, H, hC, hH, ?_⟩
  intro p hp
  obtain ⟨K, hK, _, _, _⟩ := hpairs p hp
  refine ⟨K, hK, ?_⟩
  intro r hr
  exact originGreen_value_slope_norm_le K a b C M hC.le hM hK F hF hr

end HBL.Profile.Kummer
