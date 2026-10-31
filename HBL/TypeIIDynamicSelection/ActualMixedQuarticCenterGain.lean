import HBL.TypeIIDynamicSelection.ActualMixedQuarticGain
import Mathlib.Tactic

/-!
# Physical whole-radiation Hartree center: quantitative mixed-density gain

The preceding exact quartic expansion gives a quadratic/higher density
R_mix = |V+Z|^4 - |V|^4 - |Z|^4 - 4 V^3 Re Z.

The uniform-in-radius pointwise estimate alone cannot be integrated on
the whole half-line. Here we combine it with a genuine radial L2(dr)
bound for the radiation. This provides an actual absolutely convergent
radial Hartree center and its time-decay estimate.

The L2(dr) bound and its decay are explicit *physical regularity inputs*,
not previously proved consequences of a selected Hartree PDE orbit.
This is a necessary source estimate for manuscript environment 2.12,
not the completion of that environment or of Type II blowup.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact physical mixed Hartree center gain, with true global
radial L2 integrability instead of integrating a constant over
an infinite spatial domain.  The assumptions are given directly
on the real bubble and the complex radiation field. -/
theorem actual_whole_radiation_mixed_center_twoBeta_gain
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    {s beta M A B : ℝ}
    (hs : 1 ≤ s) (hbeta : (1 / 2 : ℝ) < beta)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVmeas : Measurable V) (hZmeas : Measurable Z)
    (hV : ∀ rho : ℝ, 0 < rho → |V rho| ≤ M)
    (hZ : ∀ rho : ℝ, 0 < rho → ‖Z rho‖ ≤ A * s ^ (-beta))
    (hZL2 : IntegrableOn (fun rho => ‖Z rho‖ ^ 2) (Ioi (0 : ℝ)))
    (hZmass : (∫ rho in Ioi (0 : ℝ), ‖Z rho‖ ^ 2) ≤
      B * s ^ (-2 * beta)) :
    0 < 2 * beta - 1 ∧
      IntegrableOn (actualWholeRadiationMixedHigher V Z) (Ioi (0 : ℝ)) ∧
      |radialHartreeCenter (actualWholeRadiationMixedHigher V Z)| ≤
        (4 * Real.pi * hartreeKappa *
          (6 * M ^ 2 + 4 * M * A) * B) * s ^ (-2 * beta) := by
  let K : ℝ := 6 * M ^ 2 + 4 * M * A
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpow : s ^ (-beta) ≤ (1 : ℝ) := by
    have hle : -beta ≤ (0 : ℝ) := by linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hs hle
  have hbound : ∀ rho ∈ Ioi (0 : ℝ),
      |actualWholeRadiationMixedHigher V Z rho| ≤
        K * ‖Z rho‖ ^ 2 := by
    intro rho hrho
    have hZ0 : ‖Z rho‖ ≤ A := by
      calc
        ‖Z rho‖ ≤ A * s ^ (-beta) := hZ rho hrho
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hpow hA
        _ = A := by ring
    have hV2 : |V rho| ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hV rho hrho) 2
    have hprod : |V rho| * ‖Z rho‖ ≤ M * A :=
      mul_le_mul (hV rho hrho) hZ0 (norm_nonneg _) hM
    have hcoeff :
        6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖ ≤ K := by
      dsimp [K]
      nlinarith only [hV2, hprod]
    exact (actual_whole_radiation_mixed_higher_abs_le V Z rho).trans
      (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
  have hHigherMeas : Measurable
      (actualWholeRadiationMixedHigher V Z) := by
    unfold actualWholeRadiationMixedHigher
    fun_prop
  have hHigherInt :
      IntegrableOn (actualWholeRadiationMixedHigher V Z) (Ioi (0 : ℝ)) := by
    apply (hZL2.const_mul K).mono' hHigherMeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    rw [Real.norm_eq_abs]
    have hz : 0 ≤ K * ‖Z rho‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg hz]
    exact hbound rho hrho
  have hIntegral :
      |∫ rho in Ioi (0 : ℝ), actualWholeRadiationMixedHigher V Z rho| ≤
        K * B * s ^ (-2 * beta) := by
    calc
      _ ≤ ∫ rho in Ioi (0 : ℝ),
          |actualWholeRadiationMixedHigher V Z rho| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ rho in Ioi (0 : ℝ), K * ‖Z rho‖ ^ 2 := by
        apply integral_mono_ae hHigherInt.abs (hZL2.const_mul K)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact hbound rho hrho
      _ = K * ∫ rho in Ioi (0 : ℝ), ‖Z rho‖ ^ 2 := by
        rw [integral_const_mul]
      _ ≤ K * (B * s ^ (-2 * beta)) :=
        mul_le_mul_of_nonneg_left hZmass hK
      _ = K * B * s ^ (-2 * beta) := by ring
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
          (K * B * s ^ (-2 * beta)) :=
      mul_le_mul_of_nonneg_left hIntegral hkap
    _ = (4 * Real.pi * hartreeKappa *
          (6 * M ^ 2 + 4 * M * A) * B) * s ^ (-2 * beta) := by
      dsimp [K]
      ring

end HBL.TypeIIDynamicSelection
