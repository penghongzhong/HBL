import HBL.KummerOriginGreen.FrobeniusThirdJet
import HBL.KummerCompactFamily.CompactJetBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

/-- The three actual physical Frobenius coefficients needed through the
first nontrivial singular and regular matching orders. -/
def originFrobeniusCoefficientVector (p : ℝ × ℝ) : ℂ × (ℂ × ℂ) :=
  (originSingularFirstCoefficient p.1 p.2,
    (originSingularThirdCoefficient p.1 p.2,
     originRegularSecondCoefficient p.1 p.2))

/-- All coefficient-parameter derivatives are genuine Fréchet derivatives:
the coefficients were constructed algebraically from the physical frozen
operator, not supplied through a differentiability hypothesis. -/
theorem originFrobeniusCoefficientVector_contDiff :
    ContDiff ℝ ω originFrobeniusCoefficientVector := by
  unfold originFrobeniusCoefficientVector
    originSingularFirstCoefficient originSingularThirdCoefficient
    originRegularSecondCoefficient originZeroCoeff
  fun_prop

/-- For every parameter-jet order, the complete vector of actual finite
Frobenius coefficients has a uniform bound on ANY compact parameter set.
This alone does NOT assert analyticity of the infinite exact Kummer basis. -/
theorem compact_originFrobenius_all_parameter_jets_bounded
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ p ∈ A,
        ‖iteratedFDeriv ℝ n originFrobeniusCoefficientVector p‖ ≤ C := by
  exact compact_operator_parameter_jets_bounded A hA
    originFrobeniusCoefficientVector
    (fun p _ => originFrobeniusCoefficientVector_contDiff.contDiffAt)

end HBL.Profile.Kummer
