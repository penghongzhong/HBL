import HBL.KummerOriginGreen.FrobeniusFirstJet

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HBL.Profile.Kummer

/-- The next singular Frobenius coefficient from the actual frozen PDE. -/
def originSingularThirdCoefficient (mu theta : ℝ) : ℂ :=
  originZeroCoeff mu theta *
    (originZeroCoeff mu theta + Complex.I) / 24

theorem originSingularThirdCoefficient_indicial (mu theta : ℝ) :
    12 * originSingularThirdCoefficient mu theta +
      (originZeroCoeff mu theta + Complex.I) *
        originSingularFirstCoefficient mu theta = 0 := by
  unfold originSingularThirdCoefficient originSingularFirstCoefficient
  ring

def originThirdSingularValue (mu theta : ℝ) (z : ℂ) : ℂ :=
  z⁻¹ + originSingularFirstCoefficient mu theta * z +
    originSingularThirdCoefficient mu theta * z ^ 3

def originThirdSingularSlope (mu theta : ℝ) (z : ℂ) : ℂ :=
  -(z⁻¹ ^ 2) + originSingularFirstCoefficient mu theta +
    3 * originSingularThirdCoefficient mu theta * z ^ 2

def originThirdSingularSecond (mu theta : ℝ) (z : ℂ) : ℂ :=
  2 * z⁻¹ ^ 3 + 6 * originSingularThirdCoefficient mu theta * z

/-- Exact cancellation of both the singular and first-order residual terms;
the remaining source is cubic, with NO assumed special-function expansion. -/
theorem originThirdSingularResidual_exact (mu theta : ℝ)
    (z : ℂ) (hz : z ≠ 0) :
    frozenRadialJetResidual mu theta z
      (originThirdSingularValue mu theta z)
      (originThirdSingularSlope mu theta z)
      (originThirdSingularSecond mu theta z) =
    (originSingularThirdCoefficient mu theta *
      (frozenZeroCoeff mu theta + 3 * Complex.I / 2)) * z ^ 3 := by
  unfold frozenRadialJetResidual originThirdSingularValue
    originThirdSingularSlope originThirdSingularSecond
    originSingularThirdCoefficient originSingularFirstCoefficient
    originZeroCoeff frozenZeroCoeff
  push_cast
  field_simp [hz]
  ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

/-- The regular origin basis begins with the exact second-order coefficient. -/
def originRegularSecondCoefficient (mu theta : ℝ) : ℂ :=
  -(originZeroCoeff mu theta + Complex.I / 2) / 6

theorem originRegularSecondCoefficient_indicial (mu theta : ℝ) :
    6 * originRegularSecondCoefficient mu theta +
      originZeroCoeff mu theta + Complex.I / 2 = 0 := by
  unfold originRegularSecondCoefficient
  ring

def originSecondRegularValue (mu theta : ℝ) (z : ℂ) : ℂ :=
  1 + originRegularSecondCoefficient mu theta * z ^ 2

def originSecondRegularSlope (mu theta : ℝ) (z : ℂ) : ℂ :=
  2 * originRegularSecondCoefficient mu theta * z

def originSecondRegularSecond (mu theta : ℝ) : ℂ :=
  2 * originRegularSecondCoefficient mu theta

/-- The exact regular-basis second-order jet has a quadratic residual,
giving the positive spatial-order gain required for finite overlap jets. -/
theorem originSecondRegularResidual_exact (mu theta : ℝ)
    (z : ℂ) (hz : z ≠ 0) :
    frozenRadialJetResidual mu theta z
      (originSecondRegularValue mu theta z)
      (originSecondRegularSlope mu theta z)
      (originSecondRegularSecond mu theta) =
    (originRegularSecondCoefficient mu theta *
      (frozenZeroCoeff mu theta + Complex.I)) * z ^ 2 := by
  unfold frozenRadialJetResidual originSecondRegularValue
    originSecondRegularSlope originSecondRegularSecond
    originRegularSecondCoefficient originZeroCoeff frozenZeroCoeff
  push_cast
  field_simp [hz]
  ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

end HBL.Profile.Kummer
