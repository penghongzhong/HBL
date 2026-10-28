import HBL.KummerLocalInverse.SourceLinearity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_value_deriv_linear
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (a b : ℝ) (ha : a ∈ Icc (-eps) eps) (hb : b ∈ Icc (-eps) eps)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) (c : ℂ)
    {t : ℝ} (ht : t ∈ Icc (-eps) eps) :
    localAnnulusValue K a b (fun s => F s + c * G s) t = localAnnulusValue K a b F t + c * localAnnulusValue K a b G t ∧
    localAnnulusDeriv K a b (fun s => F s + c * G s) t = localAnnulusDeriv K a b F t + c * localAnnulusDeriv K a b G t := by
  have hc := localAnnulus_coefficients_linear K a b ha hb F G hF hG c ht
  constructor
  · unfold localAnnulusValue
    rw [hc.1, hc.2]
    ring
  · unfold localAnnulusDeriv
    rw [hc.1, hc.2]
    ring
end HBL.Profile.Kummer
