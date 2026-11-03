import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInnerFredholm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Correct radial conjugation: a localized r*F source with positive length gain

The raw physical interaction F is not the forcing for the half-line
unknown q=r*u. That forcing contains r*F. We retain this factor, use an
explicit auxiliary spatial cutoff, and derive a positive one-sixteenth
length gain from the accepted one-eighth estimate for F.

This cutoff is NOT the radiation-moment cutoff at 4/|c|. It equals one
on r*ell^(1/16)<=1 and vanishes on r*ell^(1/16)>=2. Its transport,
nonlocal commutators and complementary-region matching remain OPEN.
The inner solution below is a normalized Hilbert solution, not a
classical matched three-region profile. No time rate is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- An auxiliary regional localization, independent of a time law. -/
def actualHartreeConjugationCutoff (ell r : ℝ) : ℝ :=
  1 - cutoff (r * ell ^ (1 / 16 : ℝ))

/-- The radius factor required by q=r*u is retained, not discarded. -/
def actualHartreeLocalizedConjugatedSource
    (ell c : ℝ) (z : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((r * actualHartreeConjugationCutoff ell r : ℝ) : ℂ) *
    actualHartreePhysicalSliceInteraction ell c z r

theorem actualHartreeConjugationCutoff_bounds (ell r : ℝ) :
    0 ≤ actualHartreeConjugationCutoff ell r ∧
    actualHartreeConjugationCutoff ell r ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (r * ell ^ (1 / 16 : ℝ) - 1)
  have h1 := Real.smoothTransition.le_one (r * ell ^ (1 / 16 : ℝ) - 1)
  dsimp [actualHartreeConjugationCutoff, cutoff]
  constructor <;> linarith

/-- Exact inner equality and outer support, not assumed cutoff data. -/
theorem actualHartreeConjugationCutoff_regions (ell r : ℝ) :
    (r * ell ^ (1 / 16 : ℝ) ≤ 1 → actualHartreeConjugationCutoff ell r = 1) ∧
    (2 ≤ r * ell ^ (1 / 16 : ℝ) → actualHartreeConjugationCutoff ell r = 0) := by
  constructor
  · intro h
    simp only [actualHartreeConjugationCutoff, cutoff_zero_of_le_one _ h, sub_zero]
  · intro h
    simp only [actualHartreeConjugationCutoff, cutoff_one_of_two_le _ h, sub_self]

/-- Multiplying by r costs only ell^(-1/16) on this actual cutoff. -/
theorem actualHartreeConjugationCutoff_scaled_radius
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 ≤ r) :
    0 ≤ r * actualHartreeConjugationCutoff ell r ∧
    (r * actualHartreeConjugationCutoff ell r) * ell ^ (1 / 16 : ℝ) ≤ 2 := by
  obtain ⟨h0,h1⟩ := actualHartreeConjugationCutoff_bounds ell r
  have hd : 0 ≤ ell ^ (1 / 16 : ℝ) := (Real.rpow_pos_of_pos hell _).le
  refine ⟨mul_nonneg hr h0, ?_⟩
  by_cases h : 2 ≤ r * ell ^ (1 / 16 : ℝ)
  · rw [(actualHartreeConjugationCutoff_regions ell r).2 h]
    norm_num
  · have hsmall : r * ell ^ (1 / 16 : ℝ) ≤ 2 := (lt_of_not_ge h).le
    have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg hr hd)
    nlinarith

theorem actual_Hartree_localized_conjugated_source_measurable
    (ell c : ℝ) (z : ℝ → ℂ) (hz : Measurable z) :
    Measurable (actualHartreeLocalizedConjugatedSource ell c z) := by
  have hcut : Continuous (actualHartreeConjugationCutoff ell) := by
    exact continuous_const.sub
      (cutoff_contDiff_infty.continuous.comp (continuous_id.mul continuous_const))
  have hm : Measurable (fun r : ℝ => r * actualHartreeConjugationCutoff ell r) :=
    measurable_id.mul hcut.measurable
  exact (Complex.measurable_ofReal.comp hm).mul
    (actual_Hartree_physical_slice_source_measurable ell c z hz)

/-- Dividing the conjugated source by r recovers the localized physical
forcing. This is not yet an assertion about a reconstructed solution. -/
theorem actual_Hartree_localized_conjugated_source_div_radius
    (ell c r : ℝ) (z : ℝ → ℂ) (hr : 0 < r) :
    actualHartreeLocalizedConjugatedSource ell c z r / (r : ℂ) =
      (actualHartreeConjugationCutoff ell r : ℂ) *
        actualHartreePhysicalSliceInteraction ell c z r := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold actualHartreeLocalizedConjugatedSource
  rw [Complex.ofReal_mul]
  field_simp [hrC]

/-- The REQUIRED radially conjugated, localized source retains a genuine
positive length gain, without assuming a new source or potential bound. -/
theorem actual_Hartree_localized_conjugated_source_weighted_pointwise
    (B A ell c r : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hr : 0 < r) (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    affineJapaneseWeight (7 / 4 : ℝ) r *
      ‖actualHartreeLocalizedConjugatedSource ell c z r‖ ≤
    (2 * actualHartreePhysicalWeightedSourceConstant B A) *
      ell ^ (1 / 16 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by
  let m : ℝ := r * actualHartreeConjugationCutoff ell r
  let d : ℝ := ell ^ (1 / 16 : ℝ)
  let K : ℝ := actualHartreePhysicalWeightedSourceConstant B A
  have hK : 0 ≤ K := actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
  have hd : 0 ≤ d := (Real.rpow_pos_of_pos hell _).le
  obtain ⟨hm,hmd⟩ := actualHartreeConjugationCutoff_scaled_radius ell r hell hr.le
  have hNorm : ‖actualHartreeLocalizedConjugatedSource ell c z r‖ =
      m * ‖actualHartreePhysicalSliceInteraction ell c z r‖ := by
    simp only [actualHartreeLocalizedConjugatedSource, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm, m]
  have hSquare : d * d = ell ^ (1 / 8 : ℝ) := by
    dsimp [d]
    rw [← Real.rpow_add hell]
    norm_num
  have hRaw := actual_Hartree_physical_full_interaction_Japanese_pointwise
    ell c r B A hell hellOne hc hr hB hA z hz hSup hStrauss
  have hTail : 0 ≤ (1 + r) ^ (-(5 / 8 : ℝ)) := by positivity
  calc
    _ = m * (affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreePhysicalSliceInteraction ell c z r‖) := by rw [hNorm]; ring
    _ ≤ m * (K * ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ))) :=
      mul_le_mul_of_nonneg_left hRaw hm
    _ = (K * (1 + r) ^ (-(5 / 8 : ℝ)) * d) * (m * d) := by
      rw [← hSquare]
      ring
    _ ≤ (K * (1 + r) ^ (-(5 / 8 : ℝ)) * d) * 2 :=
      mul_le_mul_of_nonneg_left hmd (mul_nonneg (mul_nonneg hK hTail) hd)
    _ = (2 * actualHartreePhysicalWeightedSourceConstant B A) *
        ell ^ (1 / 16 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) := by dsimp [K,d]; ring

private theorem localized_conjugation_envelope_L2
    (S : ℝ → ℝ) (M : ℝ) (hS : Measurable S)
    (h0 : ∀ r : ℝ, 0 < r → 0 ≤ S r)
    (hP : ∀ r : ℝ, 0 < r → S r ≤ M * (1 + r) ^ (-(5 / 8 : ℝ))) :
    MemLp S 2 halfLineMeasure ∧
      (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
        M ^ 2 * (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ))) := by
  have hTail : IntegrableOn
      (fun r : ℝ => (1 + r) ^ (-(5 / 4 : ℝ))) (Ioi (0 : ℝ)) := by
    simpa only [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt (show -(5 / 4 : ℝ) < -1 by norm_num)
        (show -(1 : ℝ) < 0 by norm_num))
  have hMaj := hTail.const_mul (M ^ 2)
  have hSqMeas : AEStronglyMeasurable (fun r : ℝ => S r ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (hS.pow_const 2).aestronglyMeasurable.restrict
  have hBound (r : ℝ) (hr : 0 < r) :
      S r ^ 2 ≤ M ^ 2 * (1 + r) ^ (-(5 / 4 : ℝ)) := by
    have hSquare : ((1 + r) ^ (-(5 / 8 : ℝ))) ^ 2 =
        (1 + r) ^ (-(5 / 4 : ℝ)) := by
      calc
        _ = ((1 + r) ^ (-(5 / 8 : ℝ))) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (1 + r) ^ (-(5 / 8 : ℝ) * 2) :=
          (Real.rpow_mul (by linarith : 0 ≤ 1 + r) (-(5 / 8 : ℝ)) 2).symm
        _ = _ := by norm_num
    simpa only [mul_pow, hSquare] using pow_le_pow_left₀ (h0 r hr) (hP r hr) 2
  have hSqInt : IntegrableOn (fun r : ℝ => S r ^ 2) (Ioi (0 : ℝ)) := by
    apply hMaj.mono' hSqMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S r))]
    exact hBound r hr
  refine ⟨(memLp_two_iff_integrable_sq hS.aestronglyMeasurable.restrict).2 hSqInt, ?_⟩
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), M ^ 2 * (1 + r) ^ (-(5 / 4 : ℝ)) := by
      apply integral_mono_ae hSqInt hMaj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hBound r hr
    _ = _ := by rw [integral_const_mul]

/-- A complete derived L2 input for the radially conjugated inner source.
The bound explicitly retains the cost of localization and radial lifting. -/
theorem actual_Hartree_localized_conjugated_source_weighted_L2
    (B A ell c : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let S : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r *
      ‖actualHartreeLocalizedConjugatedSource ell c z r‖
    MemLp S 2 halfLineMeasure ∧
      (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
        ((2 * actualHartreePhysicalWeightedSourceConstant B A) * ell ^ (1 / 16 : ℝ)) ^ 2 *
          (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ))) := by
  dsimp only
  have hS : Measurable (fun r : ℝ => affineJapaneseWeight (7 / 4 : ℝ) r *
      ‖actualHartreeLocalizedConjugatedSource ell c z r‖) :=
    (affineJapaneseWeight_continuous _).measurable.mul
      (actual_Hartree_localized_conjugated_source_measurable ell c z hz).norm
  apply localized_conjugation_envelope_L2 _ _ hS
  · intro r _
    unfold affineJapaneseWeight
    positivity
  · intro r hr
    exact actual_Hartree_localized_conjugated_source_weighted_pointwise
      B A ell c r hB hA hell hellOne hc hr z hz hSup hStrauss

/-- Both source memberships and both forced charges are produced for
r*chi*F, not mistakenly for F. The normalized equations are genuine
half-line Fredholm equations; classical reconstruction is separate. -/
theorem actual_Hartree_localized_conjugated_source_unique_inner
    (B A ell c : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let Fp : ℝ → ℝ := fun r => (actualHartreeLocalizedConjugatedSource ell c z r).re
    let Fm : ℝ → ℝ := fun r => (actualHartreeLocalizedConjugatedSource ell c z r).im
    ∃ hp : InWeightedL2 (7 / 4 : ℝ) Fp,
    ∃ hm : InWeightedL2 (7 / 4 : ℝ) Fm,
      (∃! a : ℝ × ℝ,
        AffineTailOrthogonal HartreeChannel.plus Fp a.1 ∧
        AffineTailOrthogonal HartreeChannel.minus Fm a.2) ∧
      (∃! x : InnerCorrections,
        (1 - weightedBirmanSchwingerOperator) (x.1 : RealL2 halfLineMeasure) =
          weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
            (weightedSourceDataL2 (7 / 4 : ℝ) (correctedPlusSource Fp)
              (correctedPlusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) Fp hp)) ∧
        (1 - weightedPhaseBirman) (x.2 : RealL2 halfLineMeasure) =
          weightedSourceGreenOperator (7 / 4 : ℝ) (by norm_num)
            (weightedSourceDataL2 (7 / 4 : ℝ) (correctedMinusSource Fm)
              (correctedMinusSource_memWeightedL2 (7 / 4 : ℝ) (by norm_num) Fm hm))) := by
  dsimp only
  obtain ⟨hp,hm⟩ := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) (actualHartreeLocalizedConjugatedSource ell c z)
    (actual_Hartree_localized_conjugated_source_measurable ell c z hz)
    (actual_Hartree_localized_conjugated_source_weighted_L2
      B A ell c hB hA hell hellOne hc z hz hSup hStrauss).1
  refine ⟨hp,hm,?_,?_⟩
  · exact existsUnique_actual_twoChannel_affine_charges
      (7 / 4 : ℝ) (by norm_num) (by norm_num) _ _ hp hm
  · exact existsUnique_actualInner_affinelyCorrected
      (7 / 4 : ℝ) (by norm_num) (by norm_num) _ _ hp hm

end HBL.TypeIIDynamicSelection
