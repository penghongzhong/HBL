import HBL.MonopoleLogCharge

/-!
Exact Fredholm compatibility of the first monopole source.  This file joins
the source pairing `-pi/16`, the zero logarithmic charge, and the affine
charge `1/2`; hence the unique affine slope is `-pi/8` and the corrected
source is genuinely orthogonal to the scale resonance.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Source after subtracting the logarithmic model and an affine tail. -/
def monopoleCorrectedSource (ell : ℝ) (r : ℝ) : ℝ :=
  r * bubble r ^ 3 - hPlusApply monopoleLogModel r -
    ell * hPlusApply model r

theorem resonancePlus_monopoleSource_integrableOn :
    IntegrableOn (fun r : ℝ =>
      resonancePlus r * (r * bubble r ^ 3)) (Ioi 0) := by
  refine monopolePairingDensity_integrableOn.congr_fun ?_ measurableSet_Ioi
  intro r _
  exact (resonancePlus_mul_monopoleSource r).symm

theorem resonancePlus_correctedSource_integrableOn (ell : ℝ) :
    IntegrableOn (fun r : ℝ =>
      resonancePlus r * monopoleCorrectedSource ell r) (Ioi 0) := by
  have hsource := resonancePlus_monopoleSource_integrableOn
  have hlog := hPlusLogDensity_integrableOn
  have haff := hPlusAffineDensity_integrableOn.const_mul ell
  have h := (hsource.sub hlog).sub haff
  refine h.congr_fun ?_ measurableSet_Ioi
  intro r _
  simp only [Pi.sub_apply]
  unfold monopoleCorrectedSource hPlusLogDensity hPlusAffineDensity
  ring

theorem monopole_corrected_pairing_formula (ell : ℝ) :
    (∫ r in Ioi (0 : ℝ),
      resonancePlus r * monopoleCorrectedSource ell r) =
      -(Real.pi / 16) - ell / 2 := by
  have hsource := resonancePlus_monopoleSource_integrableOn
  have hlog := hPlusLogDensity_integrableOn
  have haff := hPlusAffineDensity_integrableOn.const_mul ell
  have hdensity : (fun r : ℝ =>
      resonancePlus r * monopoleCorrectedSource ell r) =
      (fun r : ℝ =>
        resonancePlus r * (r * bubble r ^ 3) -
          hPlusLogDensity r - ell * hPlusAffineDensity r) := by
    funext r
    unfold monopoleCorrectedSource hPlusLogDensity hPlusAffineDensity
    ring
  have hlogint :
      (∫ r in Ioi (0 : ℝ), hPlusLogDensity r) = 0 := by
    exact monopole_log_model_charge_eq_zero
  have haffint :
      (∫ r in Ioi (0 : ℝ), hPlusAffineDensity r) = 1 / 2 := by
    exact hPlus_affine_pairing_eq_half
  rw [hdensity]
  calc
    (∫ r in Ioi (0 : ℝ),
        resonancePlus r * (r * bubble r ^ 3) -
          hPlusLogDensity r - ell * hPlusAffineDensity r) =
        ((∫ r in Ioi (0 : ℝ),
          resonancePlus r * (r * bubble r ^ 3)) -
          (∫ r in Ioi (0 : ℝ), hPlusLogDensity r)) -
          (∫ r in Ioi (0 : ℝ), ell * hPlusAffineDensity r) := by
      have hsub1 := integral_sub hsource hlog
      have hsub2 := integral_sub (hsource.sub hlog) haff
      have htail := congrArg
        (fun z : ℝ => z -
          ∫ r in Ioi (0 : ℝ), ell * hPlusAffineDensity r) hsub1
      simpa only [Pi.sub_apply] using hsub2.trans htail
    _ = (-(Real.pi / 16) - 0) - ell * (1 / 2) := by
      rw [integral_const_mul,
        monopole_source_pairing_eq_neg_pi_div_sixteen,
        hlogint, haffint]
    _ = -(Real.pi / 16) - ell / 2 := by ring

/-- The real threshold charge selects one and only one affine coefficient. -/
theorem monopole_corrected_pairing_zero_iff (ell : ℝ) :
    (∫ r in Ioi (0 : ℝ),
      resonancePlus r * monopoleCorrectedSource ell r) = 0 ↔
      ell = -(Real.pi / 8) := by
  rw [monopole_corrected_pairing_formula]
  constructor <;> intro h
  · linarith
  · rw [h]
    ring

theorem monopole_corrected_source_orthogonal :
    (∫ r in Ioi (0 : ℝ),
      resonancePlus r *
        monopoleCorrectedSource monopoleAffineSlope r) = 0 := by
  rw [monopole_corrected_pairing_zero_iff,
    monopoleAffineSlope_eq_neg_pi_div_eight]

end HBL.Modulation.AffineTail
