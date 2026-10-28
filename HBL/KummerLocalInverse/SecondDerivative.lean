import HBL.KummerLocalInverse.ValueDerivative
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulusDeriv_hasDerivAt
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (a b : ℝ) (ha : a ∈ Icc (-eps) eps) (hb : b ∈ Icc (-eps) eps)
    (F : ℝ → ℂ) (hF : Continuous F) {t : ℝ} (ht : t ∈ Ioo (-eps) eps) :
    HasDerivAt (localAnnulusDeriv K a b F) (localAnnulusSecond K a b F t) t := by
  have hc := localAnnulus_coefficients_hasDerivAt K a b ha hb F hF ht
  have ht' : t ∈ Icc (-eps) eps := ⟨ht.1.le, ht.2.le⟩
  have h := ((K.dphi_hasDeriv t ht').mul hc.1).add ((K.dpsi_hasDeriv t ht').mul hc.2)
  convert h using 1
  · rfl
  · unfold localAnnulusSecond localAnnulusSourceA localAnnulusSourceB localAnnulusWronskian
    field_simp [K.wronskian_ne t ht']
    ring
end HBL.Profile.Kummer
