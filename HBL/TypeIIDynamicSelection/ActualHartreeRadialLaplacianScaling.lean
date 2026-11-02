import HBL.TypeIIDynamicSelection.ActualHartreeRadialDilationScaling
import Mathlib.Tactic

/-!
# Physical 3D radial Hartree Laplacian: critical-scale covariance

For the same regular complex physical Hartree radiation z,
the energy-critical rescaling Z_ell(r)=sqrt(ell)*z(ell*r)
satisfies the EXACT radial spatial-derivative identities

  Z_ell'(r)=sqrt(ell)*ell*z'(ell*r)
  Z_ell''(r)=sqrt(ell)*ell^2*z''(ell*r),
  Delta_rad Z_ell(r)=sqrt(ell)*ell^2 Delta_rad z(ell*r).

The proof works at positive physical r, with the genuine
Delta_rad=partial_rr+(2/r)partial_r, using real-to-complex
HasDerivAt.scomp twice. The second derivative of the exact regular
Hartree field is an explicit standard C2 analytic premise.

No fixed Type-II rate or model PDE source is introduced. This
connects the same true physical flow to the already verified
nonlocal critical Hartree RHS scaling.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- True second radial derivative of the physical critical complex
Hartree radiation pullback, without replacing it by formal jets. -/
theorem actual_Hartree_critical_rescaled_second_radial_deriv
    (ell r : ℝ) (z : ℝ → ℂ)
    (hz : ∀ x : ℝ, DifferentiableAt ℝ z (ell * x))
    (hz2 : DifferentiableAt ℝ (deriv z) (ell * r)) :
    deriv (deriv (rescalePhysicalRadiation ell z)) r =
      (Real.sqrt ell : ℂ) *
        ((ell : ℂ) ^ 2 * deriv (deriv z) (ell * r)) := by
  have hFirst (x : ℝ) :
      deriv (rescalePhysicalRadiation ell z) x =
        (Real.sqrt ell : ℂ) * ((ell : ℂ) * deriv z (ell * x)) :=
    actual_Hartree_critical_rescaled_radial_deriv ell x z (hz x)
  have hFirstEq :
      deriv (rescalePhysicalRadiation ell z) =
        fun x : ℝ =>
          (Real.sqrt ell : ℂ) * ((ell : ℂ) * deriv z (ell * x)) :=
    funext hFirst
  have hScale : HasDerivAt (fun x : ℝ => ell * x) ell r :=
    hasDerivAt_const_mul ell
  have hSecond : HasDerivAt
      (fun x : ℝ => deriv z (ell * x))
      ((ell : ℂ) * deriv (deriv z) (ell * r)) r := by
    simpa only [Function.comp_def, Complex.real_smul] using
      hz2.hasDerivAt.scomp r hScale
  have hProduct :=
    ((hSecond.const_mul (ell : ℂ)).const_mul (Real.sqrt ell : ℂ)).deriv
  calc
    deriv (deriv (rescalePhysicalRadiation ell z)) r =
        deriv (fun x : ℝ =>
          (Real.sqrt ell : ℂ) * ((ell : ℂ) * deriv z (ell * x))) r := by
      rw [hFirstEq]
    _ = (Real.sqrt ell : ℂ) *
        ((ell : ℂ) ^ 2 * deriv (deriv z) (ell * r)) := by
      convert hProduct using 1 <;> ring

/-- The ACTUAL three-dimensional radial Laplacian, including the
2/r first-derivative term, scales exactly like the full Hartree
nonlinearity. This is a genuine PDE lemma at every r>0. -/
theorem actual_Hartree_critical_rescaled_radial_Laplacian
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (z : ℝ → ℂ)
    (hz : ∀ x : ℝ, DifferentiableAt ℝ z (ell * x))
    (hz2 : DifferentiableAt ℝ (deriv z) (ell * r)) :
    complexRadialLaplacian (rescalePhysicalRadiation ell z) r =
      ((ell ^ 2 * Real.sqrt ell : ℝ) : ℂ) *
        complexRadialLaplacian z (ell * r) := by
  unfold complexRadialLaplacian
  rw [actual_Hartree_critical_rescaled_second_radial_deriv
        ell r z hz hz2,
      actual_Hartree_critical_rescaled_radial_deriv ell r z (hz r)]
  have he : (ell : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hell.ne'
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp [he, hrc]

end HBL.TypeIIDynamicSelection
