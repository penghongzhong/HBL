import HBL.TypeIIDynamicSelection.ActualMixedQuarticGain
import Mathlib.Tactic

/-!
# Nontrivial whole-radiation mixed Hartree center gain with uniform mass

For a genuine nonzero terminal radiation under critical scaling,
the full half-line radial L2(dr) mass does NOT decay: it is invariant.
The required quadratic Hartree source gain therefore cannot be
deduced by postulating that radial mass tends to zero.

Here the true higher mixed quartic source is controlled instead by
the radial L2 masses of both profiles (which can stay nonzero)
together with the actual pointwise smallness of radiation.
There is no remote-support assumption and no prescribed blowup rate.
The uniform L2 and pointwise decay inputs remain analytic conditions
to be obtained from a genuine Hartree PDE profile for manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Full physical mixed Hartree center has s^(-2 beta) decay even when
the total radial radiation L2 mass is only BOUNDED, not decaying.
This uses a genuine spatial integrable envelope rather than a
nonintegrable constant bound on the infinite half-line. -/
theorem actual_whole_radiation_mixed_center_uniformMass_twoBeta_gain
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    {s beta A CV CZ : ℝ}
    (hs : 1 ≤ s) (hbeta : (1 / 2 : ℝ) < beta)
    (hA : 0 ≤ A)
    (hVmeas : Measurable V) (hZmeas : Measurable Z)
    (hV2 : IntegrableOn (fun rho => |V rho| ^ 2) (Ioi (0 : ℝ)))
    (hZ2 : IntegrableOn (fun rho => ‖Z rho‖ ^ 2) (Ioi (0 : ℝ)))
    (hVmass : (∫ rho in Ioi (0 : ℝ), |V rho| ^ 2) ≤ CV)
    (hZmass : (∫ rho in Ioi (0 : ℝ), ‖Z rho‖ ^ 2) ≤ CZ)
    (hZ : ∀ rho : ℝ, 0 < rho → ‖Z rho‖ ≤ A * s ^ (-beta)) :
    0 < 2 * beta - 1 ∧
      IntegrableOn (actualWholeRadiationMixedHigher V Z) (Ioi (0 : ℝ)) ∧
      |radialHartreeCenter (actualWholeRadiationMixedHigher V Z)| ≤
        (4 * Real.pi * hartreeKappa * A ^ 2 * (8 * CV + 2 * CZ)) *
          s ^ (-2 * beta) := by
  have hScaleSquare : (s ^ (-beta)) ^ 2 = s ^ (-2 * beta) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ s) (-beta) 2]
    congr 1
    ring
  have hCoefNonneg : 0 ≤ A ^ 2 * s ^ (-2 * beta) := by positivity
  have hDominates : ∀ rho ∈ Ioi (0 : ℝ),
      |actualWholeRadiationMixedHigher V Z rho| ≤
        (A ^ 2 * s ^ (-2 * beta)) *
          (8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2) := by
    intro rho hrho
    have hcross :
        4 * |V rho| * ‖Z rho‖ ≤
          2 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2 := by
      nlinarith [sq_nonneg (|V rho| - ‖Z rho‖)]
    have hfactor :
        6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖ ≤
          8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2 := by
      linarith
    have hz2 : ‖Z rho‖ ^ 2 ≤ A ^ 2 * s ^ (-2 * beta) := by
      calc
        ‖Z rho‖ ^ 2 ≤ (A * s ^ (-beta)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hZ rho hrho) 2
        _ = A ^ 2 * s ^ (-2 * beta) := by
          rw [mul_pow, hScaleSquare]
    calc
      _ ≤ (6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖) *
          ‖Z rho‖ ^ 2 :=
        actual_whole_radiation_mixed_higher_abs_le V Z rho
      _ ≤ (8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2) *
          (A ^ 2 * s ^ (-2 * beta)) :=
        mul_le_mul hfactor hz2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hEnvelopeInt : IntegrableOn
      (fun rho => 8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2)
      (Ioi (0 : ℝ)) :=
    (hV2.const_mul (8 : ℝ)).add (hZ2.const_mul (2 : ℝ))
  have hEnvelopeMass :
      (∫ rho in Ioi (0 : ℝ),
        8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2) ≤
          8 * CV + 2 * CZ := by
    have hadd := integral_add
      (hV2.const_mul (8 : ℝ)) (hZ2.const_mul (2 : ℝ))
    have hsplit :
        (∫ rho in Ioi (0 : ℝ),
          8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2) =
            8 * (∫ rho in Ioi (0 : ℝ), |V rho| ^ 2) +
              2 * (∫ rho in Ioi (0 : ℝ), ‖Z rho‖ ^ 2) := by
      simpa only [Pi.add_apply, integral_const_mul] using hadd
    rw [hsplit]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hVmass (by norm_num))
      (mul_le_mul_of_nonneg_left hZmass (by norm_num))
  have hDominatingInt : IntegrableOn
      (fun rho => (A ^ 2 * s ^ (-2 * beta)) *
        (8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2))
      (Ioi (0 : ℝ)) :=
    hEnvelopeInt.const_mul (A ^ 2 * s ^ (-2 * beta))
  have hHigherMeas : Measurable
      (actualWholeRadiationMixedHigher V Z) := by
    unfold actualWholeRadiationMixedHigher
    fun_prop
  have hHigherInt : IntegrableOn
      (actualWholeRadiationMixedHigher V Z) (Ioi (0 : ℝ)) := by
    apply hDominatingInt.mono' hHigherMeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    have hpos : 0 ≤ (A ^ 2 * s ^ (-2 * beta)) *
        (8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2) := by
      positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using
      hDominates rho hrho
  have hIntegral :
      |∫ rho in Ioi (0 : ℝ),
          actualWholeRadiationMixedHigher V Z rho| ≤
        A ^ 2 * (8 * CV + 2 * CZ) * s ^ (-2 * beta) := by
    calc
      _ ≤ ∫ rho in Ioi (0 : ℝ),
          |actualWholeRadiationMixedHigher V Z rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi (0 : ℝ),
          (A ^ 2 * s ^ (-2 * beta)) *
            (8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2) := by
        apply integral_mono_ae hHigherInt.abs hDominatingInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hDominates rho hrho
      _ = (A ^ 2 * s ^ (-2 * beta)) *
          (∫ rho in Ioi (0 : ℝ),
            8 * |V rho| ^ 2 + 2 * ‖Z rho‖ ^ 2) := by
        rw [integral_const_mul]
      _ ≤ (A ^ 2 * s ^ (-2 * beta)) *
          (8 * CV + 2 * CZ) :=
        mul_le_mul_of_nonneg_left hEnvelopeMass hCoefNonneg
      _ = A ^ 2 * (8 * CV + 2 * CZ) * s ^ (-2 * beta) := by
        ring
  have hkap : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  refine ⟨by linarith, hHigherInt, ?_⟩
  calc
    |radialHartreeCenter (actualWholeRadiationMixedHigher V Z)| =
        (4 * Real.pi * hartreeKappa) *
          |∫ rho in Ioi (0 : ℝ),
            actualWholeRadiationMixedHigher V Z rho| := by
      unfold radialHartreeCenter
      rw [abs_mul, abs_of_nonneg hkap]
    _ ≤ (4 * Real.pi * hartreeKappa) *
          (A ^ 2 * (8 * CV + 2 * CZ) * s ^ (-2 * beta)) :=
      mul_le_mul_of_nonneg_left hIntegral hkap
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
