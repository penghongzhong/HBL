import HBL.TypeIIDynamicSelection.ActualMixedQuarticRieszGain
import HBL.TypeIIDynamicSelection.ActualPhysicalQuadraticRiesz
import Mathlib.Tactic

/-!
# Actual physical rescaled radiation: mixed Riesz row and first-layer smallness

No blowup exponent or terminal modulation speed is prescribed.  The exact
physical radiation is Z_ell(y) = sqrt(ell) * z(ell*y), ell>0.

The actual logarithmic Hartree row is bounded for the bubble plus genuine
regular radiation by two previously proved physical kernels.  A genuine
row-integrability input for the transformed radiation is displayed
separately; it will be discharged when the full regular-radiation
function class is built. This does not close original manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- The actual mixed source envelope for the stationary bubble and
energy-critical regular radiation has a uniformly r-normalized
Hartree logarithmic row, independent of the physical length ell.
Its numerical upper bound is DERIVED from the regular radiation
bubble-squared decay and the original physical Hartree kernel. -/
theorem physical_bubble_mixed_envelope_uniform_row
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (z : ℝ → ℂ) (hz : Measurable z)
    {C : ℝ} (hC : 0 ≤ C)
    (hzdecay : ∀ u : ℝ, 0 < u → ‖z u‖ ^ 2 ≤ C * bubble u ^ 2)
    (hZrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖rescalePhysicalRadiation ell z rho‖ ^ 2) (Ioi (0 : ℝ))) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope
          bubble (rescalePhysicalRadiation ell z) rho)
      (Ioi (0 : ℝ)) ∧
    (∫ rho in Ioi (0 : ℝ),
      rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope
          bubble (rescalePhysicalRadiation ell z) rho) ≤
      r * radialHartreeBubbleBoundConstant * (8 + 2 * C) := by
  have hW := radialHartreeBubble_integrable_bound hr
  have hZR := physicalRadiation_quadratic_Riesz_row_uniform_of_profile
    ell hell r hr z hz hC hzdecay
  have hRowEq :
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope
          bubble (rescalePhysicalRadiation ell z) rho) =
      (fun rho => (8 : ℝ) *
        (rho * hartreeRadialLog r rho * bubble rho ^ 2) +
          2 * (rho * hartreeRadialLog r rho *
            ‖rescalePhysicalRadiation ell z rho‖ ^ 2)) := by
    funext rho
    unfold actualWholeRadiationMixedEnvelope
    rw [sq_abs]
    ring
  have hRowInt : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope
          bubble (rescalePhysicalRadiation ell z) rho) (Ioi (0 : ℝ)) := by
    rw [hRowEq]
    exact (hW.1.const_mul (8 : ℝ)).add (hZrow.const_mul (2 : ℝ))
  refine ⟨hRowInt, ?_⟩
  rw [hRowEq]
  have hadd := integral_add
    (hW.1.const_mul (8 : ℝ)) (hZrow.const_mul (2 : ℝ))
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_const_mul, integral_const_mul]
  calc
    (8 : ℝ) * (∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho * bubble rho ^ 2) +
      2 * (∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho *
          ‖rescalePhysicalRadiation ell z rho‖ ^ 2) ≤
      8 * (r * radialHartreeBubbleBoundConstant) +
        2 * (r * radialHartreeBubbleBoundConstant * C) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hW.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hZR (by norm_num))
    _ = r * radialHartreeBubbleBoundConstant * (8 + 2 * C) := by ring

/-- The genuinely nonlinear mixed-density Hartree potential of
physical regular radiation is O(ell), NOT O(s^{-chosen exponent}).
The length ell is free to be selected by the full PDE/modulation flow.
The actual physical weighted row is an explicit analytic input. -/
theorem physical_mixed_higher_Riesz_linear_length
    (V : ℝ → ℝ) (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (z : ℝ → ℂ) (hVmeas : Measurable V) (hz : Measurable z)
    {A J : ℝ}
    (hzBound : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ A)
    (hEnvelope : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope
          V (rescalePhysicalRadiation ell z) rho) (Ioi (0 : ℝ)))
    (hEnvelopeBound :
      (∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedEnvelope
            V (rescalePhysicalRadiation ell z) rho) ≤ r * J) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher
          V (rescalePhysicalRadiation ell z) rho) (Ioi (0 : ℝ)) ∧
    |radialHartreePotential
        (actualWholeRadiationMixedHigher
          V (rescalePhysicalRadiation ell z)) r| ≤
      (2 * Real.pi * hartreeKappa * A ^ 2 * J) * ell := by
  let Z := rescalePhysicalRadiation ell z
  have hZmeas : Measurable Z := by
    dsimp [Z]
    unfold rescalePhysicalRadiation
    exact measurable_const.mul (hz.comp (measurable_const.mul measurable_id))
  have hFmeas : Measurable (actualWholeRadiationMixedHigher V Z) := by
    unfold actualWholeRadiationMixedHigher
    fun_prop
  have hLogMeas : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hTime : 0 ≤ ell * A ^ 2 := by positivity
  have hPoint : ∀ rho ∈ Ioi (0 : ℝ),
      |actualWholeRadiationMixedHigher V Z rho| ≤
        (ell * A ^ 2) * actualWholeRadiationMixedEnvelope V Z rho := by
    intro rho hrho
    have hZ2 : ‖Z rho‖ ^ 2 ≤ ell * A ^ 2 := by
      dsimp [Z]
      rw [physicalRadiation_rescale_quadratic ell hell z rho]
      apply mul_le_mul_of_nonneg_left _ hell.le
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hzBound (ell * rho) (mul_pos hell hrho)) 2
    have hcross :
        4 * |V rho| * ‖Z rho‖ ≤
          2 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2 := by
      nlinarith [sq_nonneg (|V rho| - ‖Z rho‖)]
    have hfactor :
        6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖ ≤
          actualWholeRadiationMixedEnvelope V Z rho := by
      dsimp [actualWholeRadiationMixedEnvelope]
      linarith
    calc
      _ ≤ (6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖) *
        ‖Z rho‖ ^ 2 :=
        actual_whole_radiation_mixed_higher_abs_le V Z rho
      _ ≤ actualWholeRadiationMixedEnvelope V Z rho * (ell * A ^ 2) :=
        mul_le_mul hfactor hZ2 (sq_nonneg _) (by
          dsimp [actualWholeRadiationMixedEnvelope]; positivity)
      _ = _ := by ring
  have hWeighted : ∀ rho ∈ Ioi (0 : ℝ),
      |rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher V Z rho| ≤
      (ell * A ^ 2) * (rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope V Z rho) := by
    intro rho hrho
    have hLogPos : 0 ≤ hartreeRadialLog r rho :=
      hartreeRadialLog_nonneg r rho hr hrho
    have hKernel : 0 ≤ rho * hartreeRadialLog r rho :=
      mul_nonneg hrho.le hLogPos
    calc
      _ = rho * hartreeRadialLog r rho *
        |actualWholeRadiationMixedHigher V Z rho| := by
          rw [abs_mul, abs_mul, abs_of_pos hrho, abs_of_nonneg hLogPos]
      _ ≤ (rho * hartreeRadialLog r rho) *
          ((ell * A ^ 2) * actualWholeRadiationMixedEnvelope V Z rho) :=
        mul_le_mul_of_nonneg_left (hPoint rho hrho) hKernel
      _ = _ := by ring
  have hRowMeas : Measurable (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher V Z rho) :=
    (measurable_id.mul hLogMeas).mul hFmeas
  have hRowInt : IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      actualWholeRadiationMixedHigher V Z rho) (Ioi (0 : ℝ)) := by
    apply (hEnvelope.const_mul (ell * A ^ 2)).mono'
      hRowMeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    have hnonneg : 0 ≤ (ell * A ^ 2) *
        (rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedEnvelope V Z rho) := by
      have hlog := hartreeRadialLog_nonneg r rho hr hrho
      have henv : 0 ≤ actualWholeRadiationMixedEnvelope V Z rho := by
        unfold actualWholeRadiationMixedEnvelope
        positivity
      exact mul_nonneg hTime
        (mul_nonneg (mul_nonneg hrho.le hlog) henv)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
      hWeighted rho hrho
  have hInt : |∫ rho in Ioi (0 : ℝ),
      rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher V Z rho| ≤
      ell * A ^ 2 * (r * J) := by
    calc
      _ ≤ ∫ rho in Ioi (0 : ℝ),
        |rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedHigher V Z rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi (0 : ℝ),
        (ell * A ^ 2) * (rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedEnvelope V Z rho) := by
        apply integral_mono_ae hRowInt.abs
          (hEnvelope.const_mul (ell * A ^ 2))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hWeighted rho hrho
      _ = (ell * A ^ 2) * (∫ rho in Ioi (0 : ℝ),
          rho * hartreeRadialLog r rho *
            actualWholeRadiationMixedEnvelope V Z rho) := by
        rw [integral_const_mul]
      _ ≤ (ell * A ^ 2) * (r * J) :=
        mul_le_mul_of_nonneg_left hEnvelopeBound hTime
  have hCoeff : 0 ≤ 2 * Real.pi * hartreeKappa / r := by
    unfold hartreeKappa
    positivity
  refine ⟨hRowInt, ?_⟩
  unfold radialHartreePotential
  rw [abs_mul, abs_of_nonneg hCoeff]
  calc
    _ ≤ (2 * Real.pi * hartreeKappa / r) * (ell * A ^ 2 * (r * J)) :=
      mul_le_mul_of_nonneg_left hInt hCoeff
    _ = (2 * Real.pi * hartreeKappa * A ^ 2 * J) * ell := by
      field_simp [hr.ne']

/-- A completely identified STATIONARY BUBBLE + rescaled regular
radiation consequence. A genuine regular-radiation row-integrability
input remains visible. Neither a selected rate nor an arbitrary
abstract source inverse appears in the conclusion. -/
theorem physical_bubble_mixed_Riesz_linear_length
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (z : ℝ → ℂ) (hz : Measurable z)
    {C A : ℝ} (hC : 0 ≤ C)
    (hzdecay : ∀ u : ℝ, 0 < u → ‖z u‖ ^ 2 ≤ C * bubble u ^ 2)
    (hzBound : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ A)
    (hZrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖rescalePhysicalRadiation ell z rho‖ ^ 2) (Ioi (0 : ℝ))) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher bubble
          (rescalePhysicalRadiation ell z) rho) (Ioi (0 : ℝ)) ∧
    |radialHartreePotential
        (actualWholeRadiationMixedHigher bubble
          (rescalePhysicalRadiation ell z)) r| ≤
        (2 * Real.pi * hartreeKappa * A ^ 2 *
          radialHartreeBubbleBoundConstant * (8 + 2 * C)) * ell := by
  have hE := physical_bubble_mixed_envelope_uniform_row
    ell r hell hr z hz hC hzdecay hZrow
  have hBubbleMeas : Measurable bubble :=
    bubble_contDiff_infty.continuous.measurable
  exact physical_mixed_higher_Riesz_linear_length
    bubble ell r hell hr z hBubbleMeas hz hzBound hE.1 hE.2

end HBL.TypeIIDynamicSelection
