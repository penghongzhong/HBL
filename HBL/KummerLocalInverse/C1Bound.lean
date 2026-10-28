import HBL.KummerLocalInverse.CoefficientBounds
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_value_deriv_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : LocalKummerBound K C)
    (hab : Icc a b ⊆ Icc (-eps) eps) (F : ℝ → ℂ)
    (hF : ∀ t ∈ Icc a b, ‖F t‖ ≤ M) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖localAnnulusValue K a b F t‖ + ‖localAnnulusDeriv K a b F t‖ ≤
      (2 * C ^ 3 * (b - a)) * M := by
  have hcoef := localAnnulus_coefficients_norm_le K a b C M hC hM hK hab F hF ht
  have hk := hK t (hab ht)
  have hbound (p q : ℂ) (hp : ‖p‖ ≤ C) (hq : ‖q‖ ≤ C) :
      ‖p * localAnnulusCoeffA K b F t + q * localAnnulusCoeffB K a F t‖ ≤ C ^ 3 * (b - a) * M := by
    calc
      _ ≤ ‖p‖ * ‖localAnnulusCoeffA K b F t‖ + ‖q‖ * ‖localAnnulusCoeffB K a F t‖ := by
        simpa only [norm_mul] using norm_add_le (p * localAnnulusCoeffA K b F t) (q * localAnnulusCoeffB K a F t)
      _ ≤ C * (C ^ 2 * M * (b - t)) + C * (C ^ 2 * M * (t - a)) :=
        _root_.add_le_add (mul_le_mul hp hcoef.1 (norm_nonneg _) hC)
          (mul_le_mul hq hcoef.2 (norm_nonneg _) hC)
      _ = _ := by ring
  have hv := hbound (K.phi t) (K.psi t) hk.1 hk.2.2.1
  have hd := hbound (K.dphi t) (K.dpsi t) hk.2.1 hk.2.2.2.1
  change ‖K.phi t * localAnnulusCoeffA K b F t + K.psi t * localAnnulusCoeffB K a F t‖ +
    ‖K.dphi t * localAnnulusCoeffA K b F t + K.dpsi t * localAnnulusCoeffB K a F t‖ ≤ _
  nlinarith
end HBL.Profile.Kummer
