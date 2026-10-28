import HBL.KummerLocalInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_sources_continuous
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (F : ℝ → ℂ) (hF : Continuous F) :
    (∀ t ∈ Icc (-eps) eps, ContinuousAt (localAnnulusSourceA K F) t ∧ ContinuousAt (localAnnulusSourceB K F) t) ∧
    ContinuousOn (localAnnulusSourceA K F) (Icc (-eps) eps) ∧
    ContinuousOn (localAnnulusSourceB K F) (Icc (-eps) eps) := by
  have hc (t : ℝ) (ht : t ∈ Icc (-eps) eps) :
      ContinuousAt (localAnnulusSourceA K F) t ∧ ContinuousAt (localAnnulusSourceB K F) t := by
    have hp := (K.phi_hasDeriv t ht).continuousAt
    have hdp := (K.dphi_hasDeriv t ht).continuousAt
    have hs := (K.psi_hasDeriv t ht).continuousAt
    have hds := (K.dpsi_hasDeriv t ht).continuousAt
    have hw : ContinuousAt (localAnnulusWronskian K) t := (hp.mul hds).sub (hdp.mul hs)
    exact ⟨(hs.mul hF.continuousAt).div hw (K.wronskian_ne t ht),
      (hp.mul hF.continuousAt).div hw (K.wronskian_ne t ht)⟩
  exact ⟨hc, fun t ht => (hc t ht).1.continuousWithinAt, fun t ht => (hc t ht).2.continuousWithinAt⟩
end HBL.Profile.Kummer
