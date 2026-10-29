import HBL.KummerOriginGreen.FrobeniusThirdJet
import HBL.KummerOriginBasis.CompactBasis

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- Exact physical cubic residual norm of the finite singular Frobenius jet. -/
theorem originThirdSingularResidual_norm (mu theta r : ℝ) (hr : 0 < r) :
    ‖frozenRadialJetResidual mu theta (r : ℂ)
      (originThirdSingularValue mu theta (r : ℂ))
      (originThirdSingularSlope mu theta (r : ℂ))
      (originThirdSingularSecond mu theta (r : ℂ))‖ =
    ‖originSingularThirdCoefficient mu theta *
      (frozenZeroCoeff mu theta + 3 * Complex.I / 2)‖ * r ^ 3 := by
  rw [originThirdSingularResidual_exact mu theta (r : ℂ)
    (Complex.ofReal_ne_zero.mpr hr.ne')]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]

/-- Exact quadratic residual norm for the regular physical Frobenius jet. -/
theorem originSecondRegularResidual_norm (mu theta r : ℝ) (hr : 0 < r) :
    ‖frozenRadialJetResidual mu theta (r : ℂ)
      (originSecondRegularValue mu theta (r : ℂ))
      (originSecondRegularSlope mu theta (r : ℂ))
      (originSecondRegularSecond mu theta)‖ =
    ‖originRegularSecondCoefficient mu theta *
      (frozenZeroCoeff mu theta + Complex.I)‖ * r ^ 2 := by
  rw [originSecondRegularResidual_exact mu theta (r : ℂ)
    (Complex.ofReal_ne_zero.mpr hr.ne')]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]

/-- A SINGLE coefficient bound on any compact real (mu,theta) parameter set
controls both actual frozen polynomial residuals at all positive radii.
It does not assume a PDE remainder or parameter-differentiability theorem. -/
theorem exists_compact_originFrobenius_residual_bound
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ A, ∀ r : ℝ, 0 < r →
      ‖frozenRadialJetResidual p.1 p.2 (r : ℂ)
        (originThirdSingularValue p.1 p.2 (r : ℂ))
        (originThirdSingularSlope p.1 p.2 (r : ℂ))
        (originThirdSingularSecond p.1 p.2 (r : ℂ))‖ ≤ C * r ^ 3 ∧
      ‖frozenRadialJetResidual p.1 p.2 (r : ℂ)
        (originSecondRegularValue p.1 p.2 (r : ℂ))
        (originSecondRegularSlope p.1 p.2 (r : ℂ))
        (originSecondRegularSecond p.1 p.2)‖ ≤ C * r ^ 2 := by
  let f : ℝ × ℝ → ℝ := fun p =>
    ‖originSingularThirdCoefficient p.1 p.2 *
      (frozenZeroCoeff p.1 p.2 + 3 * Complex.I / 2)‖ +
    ‖originRegularSecondCoefficient p.1 p.2 *
      (frozenZeroCoeff p.1 p.2 + Complex.I)‖
  have hcont : Continuous f := by
    dsimp [f, originSingularThirdCoefficient, originRegularSecondCoefficient,
      originZeroCoeff, frozenZeroCoeff]
    fun_prop
  obtain ⟨M, hM⟩ := hA.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro p hp r hr
  have hfp : f p ≤ M := by
    have hf0 : 0 ≤ f p := by dsimp [f]; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hf0] using hM p hp
  have hsing : ‖originSingularThirdCoefficient p.1 p.2 *
      (frozenZeroCoeff p.1 p.2 + 3 * Complex.I / 2)‖ ≤ max M 1 := by
    calc
      _ ≤ f p := by dsimp [f]; exact le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ M := hfp
      _ ≤ max M 1 := le_max_left _ _
  have hreg : ‖originRegularSecondCoefficient p.1 p.2 *
      (frozenZeroCoeff p.1 p.2 + Complex.I)‖ ≤ max M 1 := by
    calc
      _ ≤ f p := by dsimp [f]; exact le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ M := hfp
      _ ≤ max M 1 := le_max_left _ _
  constructor
  · rw [originThirdSingularResidual_norm p.1 p.2 r hr]
    exact mul_le_mul_of_nonneg_right hsing (pow_nonneg hr.le 3)
  · rw [originSecondRegularResidual_norm p.1 p.2 r hr]
    exact mul_le_mul_of_nonneg_right hreg (pow_nonneg hr.le 2)

end HBL.Profile.Kummer
