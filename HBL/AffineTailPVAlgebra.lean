import HBL.AffineTailPlusLocalZeroMode

/-!
Algebraic part of the singular radial logarithmic integral.
For r>0 the remaining integral is evaluated by cutting at rho=r and
integrating by parts. The following kernel-density identity and rational
partial fractions are formalized first, without assuming the principal-value
limit or any improper-integral exchange.
-/

noncomputable section

namespace HBL.Modulation.AffineTail

/-- Exact rational density of the scaling resonance in the Hartree kernel. -/
theorem bubble_cube_mul_scale_eq_rational (rho : ℝ) :
    bubble rho ^ 3 * resonancePlus rho =
      rho * (1 - rho ^ 2) / (2 * (1 + rho ^ 2) ^ 3) := by
  rw [resonancePlus_def, dilationGenerator_bubble_closed]
  have hsne : Real.sqrt (1 + rho ^ 2) ≠ 0 := by positivity
  have hs2 : Real.sqrt (1 + rho ^ 2) ^ 2 = 1 + rho ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs6 :
      Real.sqrt (1 + rho ^ 2) ^ 6 = (1 + rho ^ 2) ^ 3 := by
    calc
      Real.sqrt (1 + rho ^ 2) ^ 6 =
          (Real.sqrt (1 + rho ^ 2) ^ 2) ^ 3 := by ring
      _ = (1 + rho ^ 2) ^ 3 := by rw [hs2]
  unfold bubble
  rw [← hs6]
  field_simp [hsne]
  ring

/-- Reduction of the Hartree bilinear integrand to a single rational-log
integrand. This is an exact pointwise identity for all real inputs. -/
theorem hartree_scale_log_density (r rho : ℝ) :
    hartreeKernel r rho * resonancePlus rho =
      (8 * Real.pi * hartreeKappa * bubble r ^ 3) *
        (rho * (1 - rho ^ 2) / (2 * (1 + rho ^ 2) ^ 3)) *
          Real.log ((r + rho) / |r - rho|) := by
  calc
    hartreeKernel r rho * resonancePlus rho =
        (8 * Real.pi * hartreeKappa * bubble r ^ 3) *
          (bubble rho ^ 3 * resonancePlus rho) *
            Real.log ((r + rho) / |r - rho|) := by
          unfold hartreeKernel
          ring
    _ = _ := by rw [bubble_cube_mul_scale_eq_rational]

/-- Rational partial fractions governing the Cauchy principal-value
integral after integration by parts at the diagonal rho=r. -/
theorem affine_log_PV_rational_decomposition
    (r rho : ℝ) (hsep : r ^ 2 - rho ^ 2 ≠ 0) :
    rho ^ 2 / ((1 + rho ^ 2) ^ 2 * (r ^ 2 - rho ^ 2)) =
      (r ^ 2) / ((1 + r ^ 2) ^ 2 * (1 + rho ^ 2)) -
      1 / ((1 + r ^ 2) * (1 + rho ^ 2) ^ 2) +
      (r ^ 2) / ((1 + r ^ 2) ^ 2 * (r ^ 2 - rho ^ 2)) := by
  have hr : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have hρ : (1 + rho ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hr, hρ, hsep]
  ring

end HBL.Modulation.AffineTail
