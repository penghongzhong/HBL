import HBL.KummerFrozenBridge
import HBL.KummerOriginBasis.Definitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HBL.Profile.Kummer

/-- The exact first singular Frobenius coefficient, as determined by
the physical frozen Kummer equation, not postulated as a special-function
asymptotic. -/
def originSingularFirstCoefficient (mu theta : ℝ) : ℂ :=
  -(originZeroCoeff mu theta) / 2

theorem originSingularFirstCoefficient_formula (mu theta : ℝ) :
    originSingularFirstCoefficient mu theta =
      -(theta : ℂ) / 2 + Complex.I * ((mu : ℂ) + 1 / 4) / 2 := by
  unfold originSingularFirstCoefficient originZeroCoeff
  ring

theorem originSingularFirstCoefficient_indicial (mu theta : ℝ) :
    2 * originSingularFirstCoefficient mu theta +
      originZeroCoeff mu theta = 0 := by
  unfold originSingularFirstCoefficient
  ring

/-- An explicit first Frobenius jet in the actual complex radial coordinate. -/
def originFirstSingularValue (mu theta : ℝ) (z : ℂ) : ℂ :=
  z⁻¹ + originSingularFirstCoefficient mu theta * z

def originFirstSingularSlope (mu theta : ℝ) (z : ℂ) : ℂ :=
  -(z⁻¹ ^ 2) + originSingularFirstCoefficient mu theta

def originFirstSingularSecond (z : ℂ) : ℂ :=
  2 * z⁻¹ ^ 3

/-- The exact residual of the first singular Frobenius jet. The resonant
z^{-1} term cancels; the forcing is precisely a multiple of z.
This is the key input to a weighted overlap remainder estimate. -/
theorem originFirstSingularResidual_exact (mu theta : ℝ)
    (z : ℂ) (hz : z ≠ 0) :
    frozenRadialJetResidual mu theta z
      (originFirstSingularValue mu theta z)
      (originFirstSingularSlope mu theta z)
      (originFirstSingularSecond z) =
    (originSingularFirstCoefficient mu theta *
      (frozenZeroCoeff mu theta + Complex.I / 2)) * z := by
  unfold frozenRadialJetResidual originFirstSingularValue
    originFirstSingularSlope originFirstSingularSecond
    originSingularFirstCoefficient originZeroCoeff frozenZeroCoeff
  field_simp [hz]
  ring_nf

/-- Parameter differences of the required first overlap coefficient are
exactly linear, with no assumptions about an abstract parameter family. -/
theorem originSingularFirstCoefficient_difference
    (mu theta nu phi : ℝ) :
    originSingularFirstCoefficient mu theta -
      originSingularFirstCoefficient nu phi =
      -((theta : ℂ) - (phi : ℂ)) / 2 +
        Complex.I * ((mu : ℂ) - (nu : ℂ)) / 2 := by
  simp only [originSingularFirstCoefficient_formula]
  ring

end HBL.Profile.Kummer
