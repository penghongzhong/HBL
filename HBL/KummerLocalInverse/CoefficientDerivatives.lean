import HBL.KummerLocalInverse.SourceRegularity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_coefficients_hasDerivAt
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (a b : ℝ) (ha : a ∈ Icc (-eps) eps) (hb : b ∈ Icc (-eps) eps)
    (F : ℝ → ℂ) (hF : Continuous F) {t : ℝ} (ht : t ∈ Ioo (-eps) eps) :
    HasDerivAt (localAnnulusCoeffA K b F) (-localAnnulusSourceA K F t) t ∧
    HasDerivAt (localAnnulusCoeffB K a F) (localAnnulusSourceB K F t) t := by
  have hc := localAnnulus_sources_continuous K F hF
  have ht' : t ∈ Icc (-eps) eps := ⟨ht.1.le, ht.2.le⟩
  have hmA := hc.2.1.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc t
  have hmB := hc.2.2.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc t
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht.1 ht.2)] at hmA hmB
  exact ⟨intervalIntegral.integral_hasDerivAt_left
    (hc.2.1.mono (uIcc_subset_Icc ht' hb)).intervalIntegrable hmA (hc.1 t ht').1,
    intervalIntegral.integral_hasDerivAt_right
    (hc.2.2.mono (uIcc_subset_Icc ha ht')).intervalIntegrable hmB (hc.1 t ht').2⟩
end HBL.Profile.Kummer
