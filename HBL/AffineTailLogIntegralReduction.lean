import HBL.AffineTailLogPrimitive

/-!
Reduction of the real Hartree threshold zero-mode to one scalar
logarithmic integral. All theorems in this module are exact identities:
the scalar improper integral is NOT replaced by its proposed value here.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Rational logarithmic density after radial angular integration. -/
def affineLogDensity (r rho : ℝ) : ℝ :=
  (rho * (1 - rho ^ 2) / (2 * (1 + rho ^ 2) ^ 3)) *
    Real.log ((r + rho) / |r - rho|)

/-- The remaining one-dimensional Hartree integral. -/
def affineLogIntegral (r : ℝ) : ℝ :=
  ∫ rho in Ioi (0 : ℝ), affineLogDensity r rho

/-- The logarithmic density is exactly the derivative of its rational
primitive times the original Hartree logarithmic kernel. -/
theorem affineLogDensity_primitive_deriv (r rho : ℝ) :
    affineLogDensity r rho =
      deriv radialLogPrimitive rho *
        Real.log ((r + rho) / |r - rho|) := by
  rw [(radialLogPrimitive_hasDerivAt rho).deriv]
  rfl

/-- Away from the two logarithmic singularities the ratio-logarithm
equals the difference of two real logarithms. -/
theorem radialLog_ratio_eq_sub
    (r rho : ℝ) (hplus : r + rho ≠ 0) (hminus : r - rho ≠ 0) :
    Real.log ((r + rho) / |r - rho|) =
      Real.log (r + rho) - Real.log (r - rho) := by
  rw [Real.log_div hplus (abs_ne_zero.mpr hminus), Real.log_abs]

/-- The true nonlocal Hartree operator on the scale resonance is precisely
a nonzero scalar multiple of the remaining one-dimensional integral. -/
theorem nonlocalApply_resonancePlus_factor (r : ℝ) :
    nonlocalApply resonancePlus r =
      (8 * Real.pi * hartreeKappa * bubble r ^ 3) *
        affineLogIntegral r := by
  unfold nonlocalApply affineLogIntegral
  calc
    (∫ rho in Ioi (0 : ℝ), hartreeKernel r rho * resonancePlus rho) =
        ∫ rho in Ioi (0 : ℝ),
          (8 * Real.pi * hartreeKappa * bubble r ^ 3) *
            affineLogDensity r rho := by
        apply integral_congr_ae
        filter_upwards with rho
        rw [hartree_scale_log_density r rho]
        unfold affineLogDensity
        ring
    _ = _ := by rw [integral_const_mul]

end HBL.Modulation.AffineTail
