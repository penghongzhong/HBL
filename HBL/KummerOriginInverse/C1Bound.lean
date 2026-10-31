import HBL.KummerOriginInverse.CoefficientBound

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace HBL.Profile.Kummer

def originAnnulusValue {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b : ℝ)
    (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalValue K.y r * originAnnulusCoeffA K b F r +
    originPhysicalValue K.x r * originAnnulusCoeffB K a F r

def originAnnulusSlope {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b : ℝ)
    (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalSlope K.y K.dy r * originAnnulusCoeffA K b F r +
    originPhysicalSlope K.x K.dx r * originAnnulusCoeffB K a F r

theorem originAnnulus_value_slope_norm_le {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Icc a b, ‖F r‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ‖originAnnulusValue K a b F r‖ +
        ‖originAnnulusSlope K a b F r‖ ≤
      (2 * C ^ 3 * (b - a)) * M := by
  have hcoeff := originAnnulus_coefficients_norm_le K a b C M hC hM hK F hF hr
  obtain ⟨_, _, _, _, _, _, hphi, hdphi, hpsi, hdpsi, _⟩ := hK r hr
  have hbound (p q : ℂ) (hp : ‖p‖ ≤ C) (hq : ‖q‖ ≤ C) :
      ‖p * originAnnulusCoeffA K b F r +
        q * originAnnulusCoeffB K a F r‖ ≤ C ^ 3 * (b - a) * M := by
    calc
      _ ≤ ‖p‖ * ‖originAnnulusCoeffA K b F r‖ +
        ‖q‖ * ‖originAnnulusCoeffB K a F r‖ := by
          simpa only [norm_mul] using norm_add_le
            (p * originAnnulusCoeffA K b F r)
            (q * originAnnulusCoeffB K a F r)
      _ ≤ C * (C ^ 2 * M * (b - r)) +
        C * (C ^ 2 * M * (r - a)) :=
          _root_.add_le_add
            (mul_le_mul hp hcoeff.1 (norm_nonneg _) hC)
            (mul_le_mul hq hcoeff.2 (norm_nonneg _) hC)
      _ = _ := by ring
  have hv := hbound (originPhysicalValue K.y r)
    (originPhysicalValue K.x r) hphi hpsi
  have hd := hbound (originPhysicalSlope K.y K.dy r)
    (originPhysicalSlope K.x K.dx r) hdphi hdpsi
  change
    ‖originPhysicalValue K.y r * originAnnulusCoeffA K b F r +
      originPhysicalValue K.x r * originAnnulusCoeffB K a F r‖ +
    ‖originPhysicalSlope K.y K.dy r * originAnnulusCoeffA K b F r +
      originPhysicalSlope K.x K.dx r * originAnnulusCoeffB K a F r‖ ≤ _
  nlinarith

end HBL.Profile.Kummer
