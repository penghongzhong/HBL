import HBL.RadialTestPrimitive
import HBL.CompactTestCauchy

/-!
Energy-norm estimate for actual compact radial orthogonality tests.

This module combines the Green-type primitive identity, Cauchy--Schwarz,
and the radial conjugation's exact smooth-core isometry. As a result the
test is controlled by precisely the weighted gradient energy from the
manuscript, without making a Hardy estimate an additional assumption.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace HBL.Modulation

/-- Cauchy--Schwarz bound on the energy coordinate q=(r f)'.
Unlike the earlier direct Hardy estimate, this bound only tests the
derivative of the conjugated profile and uses a fixed L2 dual kernel. -/
theorem compactTest_energyCoordinate_bound
    (R : ℝ) (hR : 0 ≤ R) (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : ContDiff ℝ 1 f) :
    |∫ r in (0 : ℝ)..R, zeta r * radialU f r| ≤
      (∫ r, ‖testTailPrimitive R zeta r‖ ^ (2 : ℝ)
        ∂(volume.restrict (Ioc (0 : ℝ) R))) ^ ((1 : ℝ) / 2) *
      (∫ r, ‖deriv (radialU f) r‖ ^ (2 : ℝ)
        ∂(volume.restrict (Ioc (0 : ℝ) R))) ^ ((1 : ℝ) / 2) := by
  let Q : ℝ → ℝ := testTailPrimitive R zeta
  let g : ℝ → ℝ := deriv (radialU f)
  let mu : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  have hQ : Continuous Q :=
    (testTailPrimitive_contDiff_one R zeta hzeta).continuous
  have hg : Continuous g :=
    (radialU_contDiff_one f hf).continuous_deriv_one
  have hCS := compactTest_cauchySchwarz R hR Q g hQ hg
  have hBound :
      ‖∫ r, Q r * g r ∂mu‖ ≤
        ∫ r, ‖Q r‖ * ‖g r‖ ∂mu := by
    calc
      ‖∫ r, Q r * g r ∂mu‖
        ≤ ∫ r, ‖Q r * g r‖ ∂mu :=
          norm_integral_le_integral_norm _
      _ = ∫ r, ‖Q r‖ * ‖g r‖ ∂mu := by
        congr 1
        funext r
        exact norm_mul _ _
  calc
    |∫ r in (0 : ℝ)..R, zeta r * radialU f r|
        = ‖∫ r, Q r * g r ∂mu‖ := by
          rw [compactTest_energy_coordinate_identity R zeta f hzeta hf]
          rw [intervalIntegral.integral_of_le hR]
          simp only [Real.norm_eq_abs, Q, g, mu]
    _ ≤ ∫ r, ‖Q r‖ * ‖g r‖ ∂mu := hBound
    _ ≤ _ := by
      simpa [Q, g, mu] using hCS

/-- Sharp fixed-test bound in the radial homogeneous gradient energy on
the smooth compact core: the coefficient is the L2 norm of the explicit
primitive, not a generic cutoff-radius constant. -/
theorem compactTest_gradientEnergy_bound
    (R : ℝ) (hR : 0 ≤ R) (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : ContDiff ℝ 1 f)
    (hfR : f R = 0) :
    |∫ r in (0 : ℝ)..R, zeta r * radialU f r| ≤
      (∫ r, ‖testTailPrimitive R zeta r‖ ^ (2 : ℝ)
        ∂(volume.restrict (Ioc (0 : ℝ) R))) ^ ((1 : ℝ) / 2) *
      (∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2) ^
        ((1 : ℝ) / 2) := by
  have hE :
      (∫ r, ‖deriv (radialU f) r‖ ^ (2 : ℝ)
          ∂(volume.restrict (Ioc (0 : ℝ) R))) =
        ∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2 := by
    rw [← intervalIntegral.integral_of_le hR]
    calc
      (∫ r in (0 : ℝ)..R, ‖deriv (radialU f) r‖ ^ (2 : ℝ)) =
          ∫ r in (0 : ℝ)..R, (deriv (radialU f) r) ^ 2 := by
            apply intervalIntegral.integral_congr
            intro r _
            simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      _ = ∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2 :=
          radialU_energy_identity R f hf hfR
  simpa only [hE] using
    compactTest_energyCoordinate_bound R hR zeta f hzeta hf

end HBL.Modulation
