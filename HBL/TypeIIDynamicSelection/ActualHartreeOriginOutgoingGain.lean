import HBL.TypeIIDynamicSelection.ActualOriginGreenIntegrable
import HBL.TypeIIDynamicSelection.ActualHartreeKummerChargeReference

/-!
The same complete physical BASE-core/radiation Hartree interaction is now
inserted into the manuscript's ORIGINAL origin-normalized Green inverse.
The two endpoint normalizations hold exactly, not approximately. Both
Wronskian densities are genuinely integrable; the forced differential system
holds almost everywhere without a source-continuity hypothesis.

The positive 1/8 gain is uniform in the explicit spatial rescaling and over
a fixed compact parameter set on a PRESCRIBED FIXED positive annulus. No
radius-independent bound for the origin gauge is claimed. Matching to the
independently selected inner and remote solutions, all generated profile
sources and the full finite recursion are NOT conclusions of this module.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

/-- Measurability is inherited from the same three-potential physical source. -/
theorem actual_Hartree_scaled_Kummer_source_measurable
    (a ell c : ℝ) (z : ℝ → ℂ) (hz : Measurable z) :
    Measurable (actualHartreeLaplacianScaledKummerSource a ell c z) := by
  let V := monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z := rescalePhysicalRadiation ell z
  have hV : Measurable V := actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact measurable_const.mul (hz.comp (measurable_const.mul measurable_id))
  have hPhys : Measurable (actualHartreePhysicalSliceInteraction ell c z) :=
    actual_Hartree_physical_complete_interaction_measurable V Z hV hZ
  exact measurable_const.mul (hPhys.comp (measurable_const.mul measurable_id))

/-- The physical source is interval integrable on every prescribed positive
annulus. This is derived from measurability and the accepted source estimate. -/
theorem actual_Hartree_scaled_Kummer_source_intervalIntegrable
    (B A ell c a r0 r1 : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (ha : 0 < a) (hr0 : 0 < r0) (hrr : r0 ≤ r1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    IntervalIntegrable (actualHartreeLaplacianScaledKummerSource a ell c z)
      volume r0 r1 := by
  let M := actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ) / r0 ^ 2
  have hConst : IntervalIntegrable (fun _ : ℝ => M) volume r0 r1 := intervalIntegrable_const
  apply hConst.mono_fun'
    (actual_Hartree_scaled_Kummer_source_measurable a ell c z hz).aestronglyMeasurable.restrict
  rw [uIoc_of_le hrr]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact actual_Hartree_scaled_Kummer_source_annulus_bound B A ell c a r0 r
    hB hA hell hellOne hc ha hr0 hr.1.le z hz hSup hStrauss

/-- Full original-source, original-normalization conclusion on one positive
annulus. In particular both endpoint identities are exact zero identities.
No incoming/outgoing compatibility or small source assumption is supplied. -/
theorem actual_Hartree_origin_outgoing_gain_on_annulus
    (B A ell c a r0 r1 C : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (ha : 0 < a) (hr0 : 0 < r0) (hrr : r0 ≤ r1) (hC : 0 ≤ C)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    {mu theta R : ℝ} (K : OriginKummerPair mu theta R)
    (hK : OriginBasisOn K r0 r1 C) :
    let F := actualHartreeLaplacianScaledKummerSource a ell c z
    IntervalIntegrable (originGreenSourceA K F) volume r0 r1 ∧
    IntervalIntegrable (originGreenSourceB K F) volume r0 r1 ∧
    (∀ᵐ r ∂volume, r ∈ Icc r0 r1 →
      HasDerivAt (originGreenValue K r0 r1 F) (originGreenSlope K r0 r1 F r) r ∧
      HasDerivAt (originGreenSlope K r0 r1 F) (originGreenSecond K r0 r1 F r) r ∧
      originGreenSecond K r0 r1 F r +
        frozenFirstCoeff r * originGreenSlope K r0 r1 F r +
        frozenZeroCoeff mu theta * originGreenValue K r0 r1 F r = F r) ∧
    (originGreenValue K r0 r1 F r1 * originPhysicalSlope K.x K.dx r1 -
      originGreenSlope K r0 r1 F r1 * originPhysicalValue K.x r1 = 0) ∧
    (originPhysicalValue K.y r0 * originGreenSlope K r0 r1 F r0 -
      originPhysicalSlope K.y K.dy r0 * originGreenValue K r0 r1 F r0 = 0) ∧
    (∀ r ∈ Icc r0 r1,
      ‖originGreenValue K r0 r1 F r‖ + ‖originGreenSlope K r0 r1 F r‖ ≤
        (2 * C ^ 3 * (r1-r0) / r0 ^ 2) *
          actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)) := by
  let F := actualHartreeLaplacianScaledKummerSource a ell c z
  let M := actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ) / r0 ^ 2
  have hFI : IntervalIntegrable F volume r0 r1 :=
    actual_Hartree_scaled_Kummer_source_intervalIntegrable B A ell c a r0 r1
      hB hA hell hellOne hc ha hr0 hrr z hz hSup hStrauss
  have hM : 0 ≤ M := div_nonneg
    (mul_nonneg (actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA)
      (Real.rpow_nonneg hell.le _)) (sq_nonneg r0)
  have hPoint (r : ℝ) (hr : r ∈ Icc r0 r1) : ‖F r‖ ≤ M :=
    actual_Hartree_scaled_Kummer_source_annulus_bound B A ell c a r0 r
      hB hA hell hellOne hc ha hr0 hr.1 z hz hSup hStrauss
  obtain ⟨hIA,hIB⟩ := actual_origin_Green_source_integrability K hK hrr F hFI
  have hEq := actual_origin_Green_integrable_forcing_ae_equation K hK hrr F hFI
  have hEnds := originGreen_endpoint_normalization K r0 r1 F
  refine ⟨hIA,hIB,hEq,hEnds.2.2.1,hEnds.2.2.2,?_⟩
  intro r hr
  have hBound := originGreen_value_slope_norm_le K r0 r1 C M hC hM hK F hPoint hr
  exact hBound.trans_eq (by dsimp [M]; ring)

/-- Construct the genuine original basis ONCE, independently of the source.
One constant controls the complete physical source for every parameter in
the compact set and every admissible radiation, scale, and monopole.
The annulus is fixed; its constants are not silently reused at moving radii. -/
theorem exists_actual_Hartree_original_outgoing_uniform_gain
    (P : Set (ℝ × ℝ)) (hP : IsCompact P)
    (r0 r1 : ℝ) (hr0 : 0 < r0) (hrr : r0 < r1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ p ∈ P, ∃ K : OriginKummerPair p.1 p.2 (r1+1),
        OriginBasisOn K r0 r1 C ∧ OriginBasisNormalization K ∧
        ∀ (B A ell c a : ℝ), 0 ≤ B → 0 ≤ A →
          0 < ell → ell ≤ 1 → |c| ≤ 1 → 0 < a →
          ∀ (z : ℝ → ℂ), Measurable z →
            (∀ u : ℝ, 0 < u → ‖z u‖ ≤ B) →
            (∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) →
            let F := actualHartreeLaplacianScaledKummerSource a ell c z
            IntervalIntegrable (originGreenSourceA K F) volume r0 r1 ∧
            IntervalIntegrable (originGreenSourceB K F) volume r0 r1 ∧
            (∀ᵐ r ∂volume, r ∈ Icc r0 r1 →
              HasDerivAt (originGreenValue K r0 r1 F) (originGreenSlope K r0 r1 F r) r ∧
              HasDerivAt (originGreenSlope K r0 r1 F) (originGreenSecond K r0 r1 F r) r ∧
              originGreenSecond K r0 r1 F r +
                frozenFirstCoeff r * originGreenSlope K r0 r1 F r +
                frozenZeroCoeff p.1 p.2 * originGreenValue K r0 r1 F r = F r) ∧
            (originGreenValue K r0 r1 F r1 * originPhysicalSlope K.x K.dx r1 -
              originGreenSlope K r0 r1 F r1 * originPhysicalValue K.x r1 = 0) ∧
            (originPhysicalValue K.y r0 * originGreenSlope K r0 r1 F r0 -
              originPhysicalSlope K.y K.dy r0 * originGreenValue K r0 r1 F r0 = 0) ∧
            (∀ r ∈ Icc r0 r1,
              ‖originGreenValue K r0 r1 F r‖ + ‖originGreenSlope K r0 r1 F r‖ ≤
                D * actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)) := by
  obtain ⟨C, H, hC, _, hpairs⟩ :=
    exists_compact_origin_kummer_basis P hP r0 r1 hr0 hrr
  refine ⟨C, 2*C^3*(r1-r0)/r0^2, hC, ?_, ?_⟩
  · exact div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hC 3))
      (sub_pos.mpr hrr)) (pow_pos hr0 2)
  · intro p hp
    obtain ⟨K,hK,hN,_,_⟩ := hpairs p hp
    refine ⟨K,hK,hN,?_⟩
    intro B A ell c a hB hA hell hellOne hc ha z hz hSup hStrauss
    exact actual_Hartree_origin_outgoing_gain_on_annulus B A ell c a r0 r1 C
      hB hA hell hellOne hc ha hr0 hrr.le hC.le z hz hSup hStrauss K hK

end HBL.TypeIIDynamicSelection
