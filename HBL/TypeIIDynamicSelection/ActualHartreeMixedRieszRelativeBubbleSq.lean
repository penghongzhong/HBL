import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import HBL.RadialHartreeDomination
import Mathlib.Tactic

/-!
# HBL revised 2.13: preserve original positive radial Riesz kernel's spatial profile

The previously accepted mixed-quartic estimate gives
  |F_mix(rho)| <= D*sqrt(ell)*bubble(rho)^2.

Older row domination drops the radial variable, controlling the
potential only by a uniform constant. The actual radial Hartree
integral is POSITIVE on (0,infty), so the sharper exact
pointwise comparison remains valid:
  |I[F_mix](r)| <= D*sqrt(ell)*I[bubble^2](r).

This is an unconditional inequality for the same physical logarithmic
inverse-square Riesz convolution. It does not yet prove the one
remaining explicit radial estimate I[bubble^2] <= C/(1+r).
No free source, independent nonlinear assumption, prescribed Type-II
rate, or new Lean axiom is used.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The ORIGINAL radial inverse-square Hartree kernel preserves
pointwise comparison with the true bubble-squared Riesz potential.
The singular diagonal is already handled by the strict absolutely
integrable bubble-squared radial kernel row. -/
theorem actual_Hartree_Riesz_relative_bubble_sq_domination
    (F : ℝ → ℝ) (hF : Measurable F)
    (M : ℝ)
    (hBound : ∀ rho : ℝ, 0 < rho →
      |F rho| ≤ M * bubble rho ^ 2)
    (r : ℝ) (hr : 0 < r) :
    |radialHartreePotential F r| ≤
      M * radialHartreePotential (fun rho => bubble rho ^ 2) r := by
  let f : ℝ → ℝ := fun rho =>
    rho * hartreeRadialLog r rho * F rho
  let g : ℝ → ℝ := fun rho =>
    rho * hartreeRadialLog r rho * bubble rho ^ 2
  have hrow := radialHartreeBubble_integrable_bound hr
  have hlogmeas : Measurable (hartreeRadialLog r) := by
    unfold hartreeRadialLog
    fun_prop
  have hFmeas : Measurable f := by
    dsimp [f]
    exact (measurable_id.mul hlogmeas).mul hF
  have hPoint : ∀ rho ∈ Ioi (0 : ℝ),
      |f rho| ≤ M * g rho := by
    intro rho hrho
    have hlog := hartreeRadialLog_nonneg r rho hr hrho
    dsimp [f,g]
    rw [abs_mul, abs_mul, abs_of_pos hrho, abs_of_nonneg hlog]
    calc
      rho * hartreeRadialLog r rho * |F rho| ≤
        rho * hartreeRadialLog r rho * (M * bubble rho ^ 2) :=
        mul_le_mul_of_nonneg_left (hBound rho hrho)
          (mul_nonneg hrho.le hlog)
      _ = M * (rho * hartreeRadialLog r rho * bubble rho ^ 2) := by
        ring
  have hFint : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply (hrow.1.const_mul M).mono'
      hFmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [Real.norm_eq_abs]
    exact hPoint rho hrho
  have hIntegral :
      |∫ rho in Ioi (0 : ℝ), f rho| ≤
        M * (∫ rho in Ioi (0 : ℝ), g rho) := by
    calc
      |∫ rho in Ioi (0 : ℝ), f rho| ≤
        ∫ rho in Ioi (0 : ℝ), |f rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi (0 : ℝ), M * g rho := by
        apply integral_mono_ae hFint.abs (hrow.1.const_mul M)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hPoint rho hrho
      _ = M * (∫ rho in Ioi (0 : ℝ), g rho) := by
        rw [integral_const_mul]
  have hCoeff : 0 ≤ 2 * Real.pi * hartreeKappa / r := by
    unfold hartreeKappa
    positivity
  change
    |(2 * Real.pi * hartreeKappa / r) *
      (∫ rho in Ioi (0 : ℝ), f rho)| ≤
    M * ((2 * Real.pi * hartreeKappa / r) *
      (∫ rho in Ioi (0 : ℝ), g rho))
  rw [abs_mul, abs_of_nonneg hCoeff]
  calc
    (2 * Real.pi * hartreeKappa / r) *
        |∫ rho in Ioi (0 : ℝ), f rho| ≤
      (2 * Real.pi * hartreeKappa / r) *
        (M * (∫ rho in Ioi (0 : ℝ), g rho)) :=
      mul_le_mul_of_nonneg_left hIntegral hCoeff
    _ = _ := by ring

/-- The COMPLETE physical inverse-square Hartree mixed quartic
density, retaining linear, quadratic and cubic cross terms, has
the exact spatial Riesz-profile domination; the old constant-only
row bound can now be recovered afterwards but is no longer used.
The only missing spatial theorem is the elementary potential of
bubble^2 itself. -/
theorem actual_Hartree_full_mixed_Riesz_relative_bubble_sq
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    |radialHartreePotential
      (actualWholeRadiationMixedQuartic
        (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius c) c)
        (rescalePhysicalRadiation ell z)) r| ≤
      (4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
        (2 * (B + A)) +
       6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
        (2 * (B + A)) ^ 2 +
       4 * (2 + 9 * monopoleRadialBoundConstant) *
        (2 * (B + A)) ^ 3) *
      Real.sqrt ell *
        radialHartreePotential (fun rho => bubble rho ^ 2) r := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let F : ℝ → ℝ := actualWholeRadiationMixedQuartic V Z
  let D : ℝ := 4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
      (2 * (B + A)) +
      6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
      (2 * (B + A)) ^ 2 +
      4 * (2 + 9 * monopoleRadialBoundConstant) *
      (2 * (B + A)) ^ 3
  have hD : 0 ≤ D := by
    dsimp [D]
    have hMon := monopoleRadialBoundConstant_pos
    positivity
  have hV : Measurable V := by
    dsimp [V]
    exact actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable Z := by
    dsimp [Z,rescalePhysicalRadiation]
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hVc : Measurable (fun u => (V u : ℂ)) :=
    Complex.measurable_ofReal.comp hV
  have hF : Measurable F := by
    dsimp [F,actualWholeRadiationMixedQuartic]
    exact (((hVc.add hZ).norm.pow_const 4).sub
      (hVc.norm.pow_const 4)).sub (hZ.norm.pow_const 4)
  have hEnvelope : ∀ rho : ℝ, 0 < rho →
      |F rho| ≤ (D * Real.sqrt ell) * bubble rho ^ 2 := by
    intro rho hrho
    simpa only [F,V,Z,D,mul_assoc] using
      actual_Hartree_physical_full_mixed_density_bubble_squared_gain
        ell c rho B A hell hellOne hrho hc hB hA
        z hSup hStrauss
  have h := actual_Hartree_Riesz_relative_bubble_sq_domination
    F hF (D * Real.sqrt ell)
    hEnvelope r hr
  simpa only [F,V,Z,D,mul_assoc] using h

end HBL.TypeIIDynamicSelection
