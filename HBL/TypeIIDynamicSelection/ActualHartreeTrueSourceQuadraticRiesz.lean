import HBL.TypeIIDynamicSelection.ActualHartreeBoundedBackgroundQuadraticRiesz
import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import Mathlib.Tactic

/-!
# Physical moving monopole and actual scaled radiation: nonlocal Hartree Taylor source

This specializes the true inverse-square radial Hartree quadratic-density
Riesz estimate to the SAME physical background V_c + sqrt(ell)*z(ell*r).
The required global L-infinity bound is PRODUCED from the actual
monopole cutoff and the regular-radiation amplitude bound, not from
a false uniform bubble envelope for the whole field.
The correction's bubble bound is still an explicit unsolved packet input;
this is a nonlocal source estimate, NOT the complete original PDE gain.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_monopole_radiation_quadratic_density_Riesz
    (ell c B e : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (he : 0 ≤ e)
    (z H : ℝ → ℂ)
    (hz : Measurable z) (hHmeas : Measurable H)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hH : ∀ x : ℝ, 0 < x → ‖H x‖ ≤ e * bubble x)
    (r : ℝ) (hr : 0 < r) :
    let U : ℝ → ℂ := fun x =>
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c x : ℂ) +
        rescalePhysicalRadiation ell z x
    let M : ℝ := 1 + monopoleRadialBoundConstant + B
    IntegrableOn
      (fun x => x * hartreeRadialLog r x *
        actualHartreeComplexDensityRemainder (U x) (H x))
      (Ioi (0 : ℝ)) ∧
    |radialHartreePotential
      (fun x => actualHartreeComplexDensityRemainder (U x) (H x)) r| ≤
      radialHartreeRowBoundConstant *
        ((6 * M ^ 2 + 4 * M * e + e ^ 2) * e ^ 2) := by
  dsimp only
  let U : ℝ → ℂ := fun x =>
    (monopolePerturbedRadialProfile
       (monopoleQuadraticRadius c) c x : ℂ) +
       rescalePhysicalRadiation ell z x
  let M : ℝ := 1 + monopoleRadialBoundConstant + B
  have hM : 0 ≤ M := by
    dsimp [M]
    have hmon := monopoleRadialBoundConstant_pos
    positivity
  have hSqrt : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg ell
  have hSqrtOne : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hVmeas :=
    actual_Hartree_moving_monopole_measurable c
  have hUmeas : Measurable U := by
    dsimp [U, rescalePhysicalRadiation]
    fun_prop
  have hUbound (x : ℝ) (hx : 0 < x) :
      ‖U x‖ ≤ M := by
    have hVbound :
        ‖(monopolePerturbedRadialProfile
            (monopoleQuadraticRadius c) c x : ℂ)‖ ≤
          1 + monopoleRadialBoundConstant := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (monopolePerturbedRadialProfile_abs_le
          (R := monopoleQuadraticRadius c) hx hc)
    have hZbound : ‖rescalePhysicalRadiation ell z x‖ ≤ B := by
      have hnorm :
          ‖rescalePhysicalRadiation ell z x‖ =
            Real.sqrt ell * ‖z (ell * x)‖ := by
        unfold rescalePhysicalRadiation
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hSqrt]
      calc
        ‖rescalePhysicalRadiation ell z x‖ =
          Real.sqrt ell * ‖z (ell * x)‖ := hnorm
        _ ≤ Real.sqrt ell * B :=
          mul_le_mul_of_nonneg_left
            (hSup (ell * x) (mul_pos hell hx)) hSqrt
        _ ≤ 1 * B :=
          mul_le_mul_of_nonneg_right hSqrtOne hB
        _ = B := one_mul B
    calc
      ‖U x‖ ≤
          ‖(monopolePerturbedRadialProfile
              (monopoleQuadraticRadius c) c x : ℂ)‖ +
          ‖rescalePhysicalRadiation ell z x‖ := norm_add_le _ _
      _ ≤ (1 + monopoleRadialBoundConstant) + B :=
        add_le_add hVbound hZbound
      _ = M := rfl
  have hMain :=
    actual_Hartree_true_quadratic_density_Riesz_from_Linfty_background
      U H hUmeas hHmeas M e hM he hUbound hH r hr
  simpa only [U, M] using hMain

end HBL.TypeIIDynamicSelection
