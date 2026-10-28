import HBL.KummerLocalInverse.SourceBounds
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_coefficients_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : LocalKummerBound K C)
    (hab : Icc a b ⊆ Icc (-eps) eps) (F : ℝ → ℂ)
    (hF : ∀ t ∈ Icc a b, ‖F t‖ ≤ M) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖localAnnulusCoeffA K b F t‖ ≤ C ^ 2 * M * (b - t) ∧
    ‖localAnnulusCoeffB K a F t‖ ≤ C ^ 2 * M * (t - a) := by
  have hA : ‖localAnnulusCoeffA K b F t‖ ≤ C ^ 2 * M * |b - t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le ht.2] at hs
    have hst : s ∈ Icc a b := ⟨ht.1.trans hs.1.le, hs.2⟩
    exact (localAnnulus_source_norm_le K C M hC hM hK F (hab hst) (hF s hst)).1
  have hB : ‖localAnnulusCoeffB K a F t‖ ≤ C ^ 2 * M * |t - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    have hst : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    exact (localAnnulus_source_norm_le K C M hC hM hK F (hab hst) (hF s hst)).2
  simpa only [abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg (sub_nonneg.mpr ht.1)] using And.intro hA hB
end HBL.Profile.Kummer
