import HBL.TypeIIDynamicSelection.ActualHartreeBackwardRadialVolterraConjugation
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerShellGain
import Mathlib.Tactic

/-!
# Exact original Hartree/Kummer backward-Volterra parameter difference

No frozen coefficient is substituted for the physical source: the
actualMatchedScaledKummerApply expression is the original radial
Laplacian, imaginary transport and true frozenZeroCoeff, all retained.
At a shared physical radius this source-level identity identifies the
precise two parameter defects needed to estimate the difference of
two source-selected Fredholm/Kummer corrections.

These theorems are *algebraic/ODE compatibility only*. They do not
assume or conclude a global physical PDE source bound, time gain,
parametric Lipschitz continuity, a nonlinear orbit or Type-II rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Exact coefficient change of the original physical Kummer operator.
The radial Laplacian cancels, but neither the imaginary radial drift
nor the genuine zero-order coefficient is dropped. No inverse estimate. -/
theorem actual_Hartree_original_Kummer_coefficient_difference
    (mu1 theta1 mu2 theta2 a1 a2 r : ℝ) (e : ℝ → ℂ) :
    actualMatchedScaledKummerApply mu1 theta1 a1 e r -
      actualMatchedScaledKummerApply mu2 theta2 a2 e r =
    (((a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹ : ℝ) : ℝ) •
        (Complex.I * (r : ℂ) / 2 * deriv e r) +
      ((((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1) -
        (((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2)) * e r := by
  unfold actualMatchedScaledKummerApply
  simp only [Complex.real_smul]
  ring

/-- The ORIGINAL scaled Hartree/Kummer operator is linear in the field
at a fixed physical parameter, with real differentiability checked for
both first and second radial derivatives. -/
theorem actual_Hartree_original_Kummer_sub_of_classical
    (mu theta a r : ℝ) (e1 e2 : ℝ → ℂ)
    (he1 : ∀ x : ℝ, DifferentiableAt ℝ e1 x)
    (he2 : ∀ x : ℝ, DifferentiableAt ℝ e2 x)
    (he1two : DifferentiableAt ℝ (deriv e1) r)
    (he2two : DifferentiableAt ℝ (deriv e2) r) :
    actualMatchedScaledKummerApply mu theta a (fun x => e1 x - e2 x) r =
      actualMatchedScaledKummerApply mu theta a e1 r -
        actualMatchedScaledKummerApply mu theta a e2 r := by
  have hfirst (x : ℝ) :
      HasDerivAt (fun y => e1 y - e2 y) (deriv e1 x - deriv e2 x) x :=
    (he1 x).hasDerivAt.sub (he2 x).hasDerivAt
  have hnear :
      deriv (fun x => e1 x - e2 x) =ᶠ[𝓝 r]
        (fun x => deriv e1 x - deriv e2 x) := by
    filter_upwards with x
    exact (hfirst x).deriv
  have hsecond :
      HasDerivAt (deriv (fun x => e1 x - e2 x))
        (deriv (deriv e1) r - deriv (deriv e2) r) r :=
    (he1two.hasDerivAt.sub he2two.hasDerivAt).congr_of_eventuallyEq hnear
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecond.deriv, (hfirst r).deriv]
  simp only [Complex.real_smul]
  ring

/-- Exact source-driven parameter difference at the SAME physical radius.
This is the rigorously typed counterpart of the paper identity (V15);
the two inhomogeneities are the actual original-operator evaluations,
not independently postulated Lipschitz or decay envelopes. -/
theorem actual_Hartree_backward_original_parameter_source_difference
    (mu1 theta1 mu2 theta2 a1 a2 r : ℝ)
    (e1 e2 : ℝ → ℂ) (f1 f2 : ℂ)
    (he1 : ∀ x : ℝ, DifferentiableAt ℝ e1 x)
    (he2 : ∀ x : ℝ, DifferentiableAt ℝ e2 x)
    (he1two : DifferentiableAt ℝ (deriv e1) r)
    (he2two : DifferentiableAt ℝ (deriv e2) r)
    (hf1 : actualMatchedScaledKummerApply mu1 theta1 a1 e1 r = f1)
    (hf2 : actualMatchedScaledKummerApply mu2 theta2 a2 e2 r = f2) :
    actualMatchedScaledKummerApply mu1 theta1 a1
        (fun x => e1 x - e2 x) r =
      f1 - f2 -
        (((a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹ : ℝ) : ℝ) •
          (Complex.I * (r : ℂ) / 2 * deriv e2 r) -
        ((((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1) -
          (((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2)) * e2 r := by
  have hlinear :=
    actual_Hartree_original_Kummer_sub_of_classical
      mu1 theta1 a1 r e1 e2 he1 he2 he1two he2two
  have hcoeff :=
    actual_Hartree_original_Kummer_coefficient_difference
      mu1 theta1 mu2 theta2 a1 a2 r e2
  calc
    actualMatchedScaledKummerApply mu1 theta1 a1
        (fun x => e1 x - e2 x) r =
      actualMatchedScaledKummerApply mu1 theta1 a1 e1 r -
        actualMatchedScaledKummerApply mu1 theta1 a1 e2 r := hlinear
    _ = f1 - f2 -
      (actualMatchedScaledKummerApply mu1 theta1 a1 e2 r -
       actualMatchedScaledKummerApply mu2 theta2 a2 e2 r) := by
        rw [hf1, ← hf2]
        ring
    _ = _ := by rw [hcoeff]; ring

end HBL.TypeIIDynamicSelection
