import HBL.TypeIIDynamicSelection.ActualHartreeCriticalNonlinearityScaling
import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# One actual Hartree field: dynamical complex gauge covariance of the PDE

P(s)=exp(-i gamma(s)); the true time derivative P'=-i gamma_s P
is derived from the exponential chain rule, not assumed.

For the same whole complex radiation Z and the true radial Hartree
operator,
  R(P Z; b, omega-gamma_s) = P R(Z; b, omega)
at the genuine differentiable time and positive spatial radius.

The full nonlocal Hartree interaction is the ORIGINAL inverse-square
quartic Riesz potential times the local cubic. No prescribed blowup
rate, independent source, or abstract regional inverse is involved.
This is the phase leg of the physical-flow -> renormalized-residual
bridge for retained manuscript original environment 2.12.
Critical spatial scale/time chain rule and actual orbit specialization
remain explicit additional obligations.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Genuine derivative of the original dynamical phase
exp(-i gamma(s)); no phase-speed constraint is inserted. -/
theorem actual_Hartree_dynamic_unit_phase_hasDerivAt
    (gamma : ℝ → ℝ) (s gs : ℝ)
    (hgamma : HasDerivAt gamma gs s) :
    HasDerivAt (fun t : ℝ => actualHartreeUnitPhase (gamma t))
      ((-Complex.I) * (gs : ℂ) * actualHartreeUnitPhase (gamma s)) s := by
  have hReal :
      HasDerivAt (fun t : ℝ => ((-(gamma t) : ℝ) : ℂ))
        (-(gs : ℂ)) s := by
    simpa only [Pi.neg_apply, Complex.ofReal_neg] using hgamma.neg.ofReal_comp
  have hArg :
      HasDerivAt
        (fun t : ℝ => Complex.I * ((-(gamma t) : ℝ) : ℂ))
        (Complex.I * (-(gs : ℂ))) s :=
    hReal.const_mul Complex.I
  have hExp := (Complex.hasDerivAt_exp
    (Complex.I * ((-(gamma s) : ℝ) : ℂ))).comp s hArg
  convert hExp using 1
  · rfl
  · unfold actualHartreeUnitPhase
    ring

/-- Time derivative of the ACTUAL phased Hartree radiation,
including the dynamically forced -i gamma_s term. -/
theorem actual_Hartree_dynamic_phase_radiation_time_hasDerivAt
    (gamma : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (s r gs : ℝ) (zt : ℂ)
    (hgamma : HasDerivAt gamma gs s)
    (hZ : HasDerivAt (fun t : ℝ => Z t r) zt s) :
    HasDerivAt (fun t : ℝ =>
      actualHartreeUnitPhase (gamma t) * Z t r)
      (actualHartreeUnitPhase (gamma s) *
        (zt - Complex.I * (gs : ℂ) * Z s r)) s := by
  have hp := actual_Hartree_dynamic_unit_phase_hasDerivAt
    gamma s gs hgamma
  have h := hp.mul hZ
  convert h using 1; ring

/-- Original HBL radial Laplacian is complex linear under the
time-frozen physical phase; all two derivatives are justified. -/
theorem actual_Hartree_constant_phase_radial_Laplacian
    (a : ℂ) (Z : ℝ → ℂ) (r : ℝ)
    (hZ : ∀ x : ℝ, DifferentiableAt ℝ Z x)
    (hZSecond : DifferentiableAt ℝ (deriv Z) r) :
    complexRadialLaplacian (fun x => a * Z x) r =
      a * complexRadialLaplacian Z r := by
  have hFirst (x : ℝ) :
      deriv (fun y : ℝ => a * Z y) x =
        a * deriv Z x := ((hZ x).hasDerivAt.const_mul a).deriv
  have hFirstEq :
      deriv (fun y : ℝ => a * Z y) =
        fun x : ℝ => a * deriv Z x := funext hFirst
  have hSecond :
      deriv (deriv (fun y : ℝ => a * Z y)) r =
        a * deriv (deriv Z) r := by
    rw [hFirstEq]
    exact (hZSecond.hasDerivAt.const_mul a).deriv
  unfold complexRadialLaplacian
  rw [hSecond, hFirst r]
  ring

/-- Original scaling generator Lambda=1/2+r d_r has exact
complex-linear phase covariance. -/
theorem actual_Hartree_constant_phase_radial_dilation
    (a : ℂ) (Z : ℝ → ℂ) (r : ℝ)
    (hZ : DifferentiableAt ℝ Z r) :
    complexRadialDilation (fun x => a * Z x) r =
      a * complexRadialDilation Z r := by
  unfold complexRadialDilation
  rw [((hZ.hasDerivAt.const_mul a).deriv)]
  ring

/-- The SAME physical complex Hartree residual is covariant
under a genuinely time-varying phase, with the exact
omega -> omega-gamma_s compensation forced by differentiation. -/
theorem actual_Hartree_dynamic_phase_full_PDE_residual_covariant
    (gamma : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r gs : ℝ)
    (hgamma : HasDerivAt gamma gs s)
    (hZTime : DifferentiableAt ℝ (fun t : ℝ => Z t r) s)
    (hZSpace : ∀ x : ℝ, DifferentiableAt ℝ (Z s) x)
    (hZSecond : DifferentiableAt ℝ (deriv (Z s)) r) :
    complexRadialRenormalizedResidual
      (fun t x => actualHartreeUnitPhase (gamma t) * Z t x)
      b (omega - gs) s r =
        actualHartreeUnitPhase (gamma s) *
          complexRadialRenormalizedResidual Z b omega s r := by
  let a : ℂ := actualHartreeUnitPhase (gamma s)
  have hTime :
      deriv (fun t : ℝ => actualHartreeUnitPhase (gamma t) * Z t r) s =
        a * (deriv (fun t : ℝ => Z t r) s -
          Complex.I * (gs : ℂ) * Z s r) := by
    exact (actual_Hartree_dynamic_phase_radiation_time_hasDerivAt
      gamma Z s r gs (deriv (fun t : ℝ => Z t r) s)
      hgamma hZTime.hasDerivAt).deriv
  have hLap :
      complexRadialLaplacian
          (fun x => actualHartreeUnitPhase (gamma s) * Z s x) r =
        a * complexRadialLaplacian (Z s) r :=
    actual_Hartree_constant_phase_radial_Laplacian a (Z s) r
      hZSpace hZSecond
  have hDil :
      complexRadialDilation
          (fun x => actualHartreeUnitPhase (gamma s) * Z s x) r =
        a * complexRadialDilation (Z s) r :=
    actual_Hartree_constant_phase_radial_dilation a (Z s) r
      (hZSpace r)
  have hNL :
      complexRadialHartreeNonlinearity
          (fun x => actualHartreeUnitPhase (gamma s) * Z s x) r =
        a * complexRadialHartreeNonlinearity (Z s) r :=
    actual_Hartree_nonlinearity_phase_covariant (gamma s) r (Z s)
  unfold complexRadialRenormalizedResidual
  rw [hTime, hLap, hDil, hNL]
  dsimp only [a]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end HBL.TypeIIDynamicSelection
