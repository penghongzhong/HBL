import HBL.KummerParameterInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem frozenZeroCoeff_difference_norm_le (mu theta mu0 theta0 : ℝ) :
    ‖frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0‖ ≤ |mu - mu0| + |theta - theta0| := by
  have he : frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0 =
      ((theta - theta0 : ℝ) : ℂ) - Complex.I * ((mu - mu0 : ℝ) : ℂ) := by
    unfold frozenZeroCoeff
    push_cast
    ring
  rw [he]
  have h := norm_sub_le (((theta - theta0 : ℝ) : ℂ)) (Complex.I * ((mu - mu0 : ℝ) : ℂ))
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, add_comm] using h
end HBL.Profile.Kummer
