import HBL.KummerLocalInverse.CoefficientDerivatives
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulusValue_hasDerivAt
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (a b : ℝ) (ha : a ∈ Icc (-eps) eps) (hb : b ∈ Icc (-eps) eps)
    (F : ℝ → ℂ) (hF : Continuous F) {t : ℝ} (ht : t ∈ Ioo (-eps) eps) :
    HasDerivAt (localAnnulusValue K a b F) (localAnnulusDeriv K a b F t) t := by
  have hc := localAnnulus_coefficients_hasDerivAt K a b ha hb F hF ht
  have ht' : t ∈ Icc (-eps) eps := ⟨ht.1.le, ht.2.le⟩
  have h := ((K.phi_hasDeriv t ht').mul hc.1).add ((K.psi_hasDeriv t ht').mul hc.2)
  convert h using 1
  · rfl
  · unfold localAnnulusDeriv localAnnulusSourceA localAnnulusSourceB
    ring
end HBL.Profile.Kummer
