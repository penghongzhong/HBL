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
  have hfst : ContDiff ℝ ω (fun p : ℝ × ℝ => (p.1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp
        (contDiff_fst : ContDiff ℝ ω (Prod.fst : ℝ × ℝ → ℝ)))
  have hsnd : ContDiff ℝ ω (fun p : ℝ × ℝ => (p.2 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp
        (contDiff_snd : ContDiff ℝ ω (Prod.snd : ℝ × ℝ → ℝ)))
  have hq : ContDiff ℝ ω
      (fun p : ℝ × ℝ => originZeroCoeff p.1 p.2) := by
    unfold originZeroCoeff
    exact hsnd.sub
      ((contDiff_const : ContDiff ℝ ω
          (fun _ : ℝ × ℝ => (Complex.I : ℂ))).mul
        (hfst.add contDiff_const))
  have hpoly : ContDiff ℝ ω
      (fun q : ℂ => (-(q) / 2,
        (q * (q + Complex.I) / 24, -(q + Complex.I / 2) / 6))) := by
    fun_prop
  change ContDiff ℝ ω (fun p : ℝ × ℝ =>
    (-(originZeroCoeff p.1 p.2) / 2,
      (originZeroCoeff p.1 p.2 *
          (originZeroCoeff p.1 p.2 + Complex.I) / 24,
        -(originZeroCoeff p.1 p.2 + Complex.I / 2) / 6)))
  exact hpoly.comp hq

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
