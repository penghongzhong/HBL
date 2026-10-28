import HBL.KummerLocalInverse.SourceRegularity
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_coefficients_linear
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (a b : ℝ) (ha : a ∈ Icc (-eps) eps) (hb : b ∈ Icc (-eps) eps)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) (c : ℂ)
    {t : ℝ} (ht : t ∈ Icc (-eps) eps) :
    localAnnulusCoeffA K b (fun s => F s + c * G s) t = localAnnulusCoeffA K b F t + c * localAnnulusCoeffA K b G t ∧
    localAnnulusCoeffB K a (fun s => F s + c * G s) t = localAnnulusCoeffB K a F t + c * localAnnulusCoeffB K a G t := by
  have hf := localAnnulus_sources_continuous K F hF
  have hg := localAnnulus_sources_continuous K G hG
  have hA : localAnnulusSourceA K (fun s => F s + c * G s) =
      (fun s => localAnnulusSourceA K F s + c * localAnnulusSourceA K G s) := by
    funext s
    unfold localAnnulusSourceA
    ring
  have hB : localAnnulusSourceB K (fun s => F s + c * G s) =
      (fun s => localAnnulusSourceB K F s + c * localAnnulusSourceB K G s) := by
    funext s
    unfold localAnnulusSourceB
    ring
  constructor
  · unfold localAnnulusCoeffA
    rw [hA, intervalIntegral.integral_add (hf.2.1.mono (uIcc_subset_Icc ht hb)).intervalIntegrable
      ((hg.2.1.mono (uIcc_subset_Icc ht hb)).intervalIntegrable.const_mul c), intervalIntegral.integral_const_mul]
  · unfold localAnnulusCoeffB
    rw [hB, intervalIntegral.integral_add (hf.2.2.mono (uIcc_subset_Icc ha ht)).intervalIntegrable
      ((hg.2.2.mono (uIcc_subset_Icc ha ht)).intervalIntegrable.const_mul c), intervalIntegral.integral_const_mul]
end HBL.Profile.Kummer
