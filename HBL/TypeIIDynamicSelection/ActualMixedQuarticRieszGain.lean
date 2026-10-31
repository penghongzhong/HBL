import HBL.TypeIIDynamicSelection.ActualMixedQuarticCenterGain
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# Actual weighted inverse-square Hartree potential gain

This is the complete nonlocal operator on the real mixed
quadratic-and-higher quartic density, not a local surrogate.
Its positive time gain is derived from the physical complex amplitude
bound and a genuinely integrable radial Hartree row.

Unlike an infinite-half-line bound by a constant, the required spatial
assumption is the explicit *physical* weighted Riesz envelope row.
A subsequent proof for the actual three-region profile must establish
this row bound uniformly with the correct dynamical parameter weights.

The result is an unnumbered bearing component of original manuscript
2.12.  It is not a certificate of the full three-region elimination.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual spatial quadratic envelope for all bubble/radiation
mixed terms after extracting the real-linear density source. -/
def actualWholeRadiationMixedEnvelope (V : ℝ → ℝ) (Z : ℝ → ℂ)
    (rho : ℝ) : ℝ :=
  8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2

/-- Pointwise NONLOCAL Riesz source gain, with all spatial factors
displayed. In particular, no decay of total radial radiation L2 mass
is postulated. -/
theorem actual_whole_radiation_mixed_higher_weighted_gain
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    {s beta A r : ℝ}
    (hs : 1 ≤ s) (hbeta : (1 / 2 : ℝ) < beta)
    (hr : 0 < r)
    (hZ : ∀ rho : ℝ, 0 < rho →
      ‖Z rho‖ ≤ A * s ^ (-beta)) :
    0 < 2 * beta - 1 ∧
      ∀ rho : ℝ, 0 < rho →
        |rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedHigher V Z rho| ≤
          (A ^ 2 * s ^ (-2 * beta)) *
            (rho * hartreeRadialLog r rho *
              actualWholeRadiationMixedEnvelope V Z rho) := by
  have htime : 0 < 2 * beta - 1 := by linarith
  have hpow : (s ^ (-beta)) ^ 2 = s ^ (-2 * beta) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ s) (-beta) 2]
    congr 1
    ring
  refine ⟨htime, ?_⟩
  intro rho hrho
  have hcross :
      4 * |V rho| * ‖Z rho‖ ≤
        2 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2 := by
    nlinarith [sq_nonneg (|V rho| - ‖Z rho‖)]
  have hfactor :
      6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖ ≤
        actualWholeRadiationMixedEnvelope V Z rho := by
    dsimp [actualWholeRadiationMixedEnvelope]
    linarith
  have hZsq : ‖Z rho‖ ^ 2 ≤ A ^ 2 * s ^ (-2 * beta) := by
    calc
      ‖Z rho‖ ^ 2 ≤ (A * s ^ (-beta)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hZ rho hrho) 2
      _ = A ^ 2 * s ^ (-2 * beta) := by rw [mul_pow, hpow]
  have hF :
      |actualWholeRadiationMixedHigher V Z rho| ≤
        (A ^ 2 * s ^ (-2 * beta)) *
          actualWholeRadiationMixedEnvelope V Z rho := by
    calc
      _ ≤ (6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖) *
          ‖Z rho‖ ^ 2 :=
        actual_whole_radiation_mixed_higher_abs_le V Z rho
      _ ≤ actualWholeRadiationMixedEnvelope V Z rho *
          (A ^ 2 * s ^ (-2 * beta)) :=
        mul_le_mul hfactor hZsq (sq_nonneg _) (by
          dsimp [actualWholeRadiationMixedEnvelope]; positivity)
      _ = _ := by ring
  have hLog : 0 ≤ hartreeRadialLog r rho :=
    hartreeRadialLog_nonneg r rho hr hrho
  have hKernel : 0 ≤ rho * hartreeRadialLog r rho :=
    mul_nonneg hrho.le hLog
  calc
    |rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher V Z rho| =
      rho * hartreeRadialLog r rho *
        |actualWholeRadiationMixedHigher V Z rho| := by
        rw [abs_mul, abs_mul, abs_of_pos hrho, abs_of_nonneg hLog]
    _ ≤ (rho * hartreeRadialLog r rho) *
        ((A ^ 2 * s ^ (-2 * beta)) *
          actualWholeRadiationMixedEnvelope V Z rho) :=
      mul_le_mul_of_nonneg_left hF hKernel
    _ = _ := by ring

/-- The actual Riesz operator applied to the quadratic/higher Hartree
density inherits s^(-2 beta).  The extra spatial input is the
INTEGRABLE weighted row of the genuine envelope at the observation
radius, with bound J; it is neither the desired conclusion nor an
abstract source solver. -/
theorem actual_whole_radiation_mixed_Riesz_twoBeta_gain
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    {s beta A r J : ℝ}
    (hs : 1 ≤ s) (hbeta : (1 / 2 : ℝ) < beta)
    (hr : 0 < r)
    (hVmeas : Measurable V) (hZmeas : Measurable Z)
    (hZ : ∀ rho : ℝ, 0 < rho →
      ‖Z rho‖ ≤ A * s ^ (-beta))
    (hEnvelope : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope V Z rho) (Ioi (0 : ℝ)))
    (hEnvelopeBound :
      (∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedEnvelope V Z rho) ≤ J) :
    0 < 2 * beta - 1 ∧
      IntegrableOn
        (fun rho => rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedHigher V Z rho) (Ioi (0 : ℝ)) ∧
      |radialHartreePotential
        (actualWholeRadiationMixedHigher V Z) r| ≤
        (2 * Real.pi * hartreeKappa / r * A ^ 2 * J) *
          s ^ (-2 * beta) := by
  let K : ℝ := A ^ 2 * s ^ (-2 * beta)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg := actual_whole_radiation_mixed_higher_weighted_gain
    V Z hs hbeta hr hZ
  have hlog : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hF : Measurable (actualWholeRadiationMixedHigher V Z) := by
    unfold actualWholeRadiationMixedHigher
    fun_prop
  have hRowMeas :
      Measurable (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher V Z rho) :=
    (measurable_id.mul hlog).mul hF
  have hRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedHigher V Z rho) (Ioi (0 : ℝ)) := by
    apply (hEnvelope.const_mul K).mono' hRowMeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    have hnonneg : 0 ≤ K * (rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedEnvelope V Z rho) := by
      have hlog0 := hartreeRadialLog_nonneg r rho hr hrho
      dsimp [actualWholeRadiationMixedEnvelope]
      positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
      hg.2 rho hrho
  have hInt :
      |∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedHigher V Z rho| ≤ K * J := by
    calc
      _ ≤ ∫ rho in Ioi (0 : ℝ),
          |rho * hartreeRadialLog r rho *
            actualWholeRadiationMixedHigher V Z rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi (0 : ℝ),
          K * (rho * hartreeRadialLog r rho *
            actualWholeRadiationMixedEnvelope V Z rho) := by
        apply integral_mono_ae hRow.abs (hEnvelope.const_mul K)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hg.2 rho hrho
      _ = K * ∫ rho in Ioi (0 : ℝ),
        rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedEnvelope V Z rho := by
        rw [integral_const_mul]
      _ ≤ K * J :=
        mul_le_mul_of_nonneg_left hEnvelopeBound hK
  have hCoeff : 0 ≤ 2 * Real.pi * hartreeKappa / r := by
    unfold hartreeKappa
    positivity
  refine ⟨hg.1, hRow, ?_⟩
  unfold radialHartreePotential
  rw [abs_mul, abs_of_nonneg hCoeff]
  calc
    _ ≤ (2 * Real.pi * hartreeKappa / r) * (K * J) :=
      mul_le_mul_of_nonneg_left hInt hCoeff
    _ = (2 * Real.pi * hartreeKappa / r * A ^ 2 * J) *
          s ^ (-2 * beta) := by
      dsimp [K]
      ring

end HBL.TypeIIDynamicSelection
