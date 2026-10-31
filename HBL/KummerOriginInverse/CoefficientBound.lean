import HBL.KummerOriginInverse.SourceBound

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace HBL.Profile.Kummer

def originAnnulusCoeffA {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (b : ℝ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ t in r..b, originAnnulusSourceA K F t

def originAnnulusCoeffB {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a : ℝ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ t in a..r, originAnnulusSourceB K F t

theorem originAnnulus_coefficients_norm_le {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Icc a b, ‖F r‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ‖originAnnulusCoeffA K b F r‖ ≤ C ^ 2 * M * (b - r) ∧
    ‖originAnnulusCoeffB K a F r‖ ≤ C ^ 2 * M * (r - a) := by
  have hA : ‖originAnnulusCoeffA K b F r‖ ≤ C ^ 2 * M * |b - r| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hr.2] at ht
    have htr : t ∈ Icc a b := ⟨hr.1.trans ht.1.le, ht.2⟩
    exact (originAnnulus_source_norm_le K a b C M hC hM hK F htr (hF t htr)).1
  have hB : ‖originAnnulusCoeffB K a F r‖ ≤ C ^ 2 * M * |r - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hr.1] at ht
    have htr : t ∈ Icc a b := ⟨ht.1.le, ht.2.trans hr.2⟩
    exact (originAnnulus_source_norm_le K a b C M hC hM hK F htr (hF t htr)).2
  simpa only [abs_of_nonneg (sub_nonneg.mpr hr.2),
    abs_of_nonneg (sub_nonneg.mpr hr.1)] using And.intro hA hB

end HBL.Profile.Kummer
