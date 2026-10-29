import HBL.KummerPrescribedAnnulus.PhysicalDefinitions

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

/-- Coefficients after the exact substitution y(r) = r u(r). -/
def originFirstCoeff (r : ℝ) : ℂ := Complex.I * (r : ℂ) / 2

def originZeroCoeff (mu theta : ℝ) : ℂ :=
  (theta : ℂ) - Complex.I * ((mu : ℂ) + 1 / 4)

def realOriginOperator (mu theta r : ℝ) : RealKummerJet →L[ℝ] RealKummerJet :=
  realJetEntry 0 2 + realJetEntry 1 3 -
    theta • (realJetEntry 2 0 + realJetEntry 3 1) -
    (mu + 1 / 4) • (realJetEntry 2 1 - realJetEntry 3 0) +
    (r / 2) • (realJetEntry 2 3 - realJetEntry 3 2)

/-- The two regularized IVPs at the origin. No singular ODE is required at r = 0. -/
structure OriginKummerPair (mu theta R : ℝ) where
  y : ℝ → ℂ
  dy : ℝ → ℂ
  x : ℝ → ℂ
  dx : ℝ → ℂ
  y_zero : y 0 = 1
  dy_zero : dy 0 = 0
  x_zero : x 0 = 0
  dx_zero : dx 0 = 1
  y_deriv : ∀ r ∈ Icc 0 R, HasDerivWithinAt y (dy r) (Icc 0 R) r
  x_deriv : ∀ r ∈ Icc 0 R, HasDerivWithinAt x (dx r) (Icc 0 R) r
  dy_deriv : ∀ r ∈ Icc 0 R, HasDerivWithinAt dy
    (-(originFirstCoeff r * dy r + originZeroCoeff mu theta * y r)) (Icc 0 R) r
  dx_deriv : ∀ r ∈ Icc 0 R, HasDerivWithinAt dx
    (-(originFirstCoeff r * dx r + originZeroCoeff mu theta * x r)) (Icc 0 R) r

def originPhysicalValue (y : ℝ → ℂ) (r : ℝ) : ℂ := y r / (r : ℂ)

def originPhysicalSlope (y v : ℝ → ℂ) (r : ℝ) : ℂ :=
  v r / (r : ℂ) - y r / (r : ℂ) ^ 2
end HBL.Profile.Kummer
