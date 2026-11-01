import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-!
# Physical Hartree regular flow -> exact critical-scale time jet

For a genuine smooth complex radial physical radiation field z(t,r),
set Z(s,r)=sqrt(ell(s))*z(time(s),ell(s)*r).

The physical scale and clock are determined by their ACTUAL equations
  ell_s=-b(s)*ell(s),   time_s=ell(s)^2.
No Type-II blowup exponent is prescribed.

Assume the visible joint C1 derivative of the same physical field
z : (time,radius) -> Complex at the one sampled spacetime point.
The full renormalized time derivative follows by a native 2D
Frechet chain rule and the actual square-root scale derivative.

This is a physical-flow analytic boundary, not a postulated
renormalized radiation equation or a source-order inequality.
Combined with separately verified Hartree Riesz critical covariance,
the spatial Laplacian and the phase derivative it will remove
the hRadiationPDE condition from the actual 2.12 source identity.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Physical-scale/clock derivative, not a prescribed terminal rate. -/
theorem actual_Hartree_physical_scale_clock_joint_time_jet
    (ell time b : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ)
    (s r : ℝ)
    (L : (ℝ × ℝ) →L[ℝ] ℂ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
    (hJoint : HasFDerivAt
      (fun p : ℝ × ℝ => z p.1 p.2) L
        (time s, ell s * r)) :
    HasDerivAt
      (fun τ : ℝ =>
        rescalePhysicalRadiation (ell τ) (z (time τ)) r)
      ((((-(b s * ell s)) / (2 * Real.sqrt (ell s)) : ℝ) : ℂ) *
          z (time s) (ell s * r) +
        (Real.sqrt (ell s) : ℂ) *
          L ((ell s) ^ 2, (-(b s * ell s)) * r)) s := by
  have hr :
      HasDerivAt (fun τ : ℝ => ell τ * r)
        ((-(b s * ell s)) * r) s :=
    hEll.mul_const r
  have hCoord :
      HasDerivAt (fun τ : ℝ => (time τ, ell τ * r))
        ((ell s) ^ 2, (-(b s * ell s)) * r) s :=
    (hClock.hasFDerivAt.prodMk hr.hasFDerivAt).hasDerivAt
  have hAlong :
      HasDerivAt (fun τ : ℝ => z (time τ) (ell τ * r))
        (L ((ell s) ^ 2, (-(b s * ell s)) * r)) s := by
    simpa only [Function.comp_def] using
      hJoint.comp_hasDerivAt s hCoord
  have hSqrt :
      HasDerivAt (fun τ : ℝ => Real.sqrt (ell τ))
        ((-(b s * ell s)) / (2 * Real.sqrt (ell s))) s :=
    hEll.sqrt hEllPos.ne'
  have hSqrtC :
      HasDerivAt (fun τ : ℝ => (Real.sqrt (ell τ) : ℂ))
        (((-(b s * ell s)) / (2 * Real.sqrt (ell s)) : ℝ) : ℂ) s :=
    hSqrt.ofReal_comp
  have hProd := hSqrtC.mul hAlong
  change HasDerivAt
      (fun τ : ℝ => (Real.sqrt (ell τ) : ℂ) *
        z (time τ) (ell τ * r)) _ s
  convert hProd using 1
  · rfl
  · ring

/-- Explicit C1 Jacobian components of the same physical Hartree
flow yield the true time/radial derivative without adding a
second source or any forced modulation exponent. -/
theorem actual_Hartree_physical_scale_clock_explicit_time_jet
    (ell time b : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ)
    (s r : ℝ)
    (L : (ℝ × ℝ) →L[ℝ] ℂ)
    (zt zr : ℂ)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
    (hJoint : HasFDerivAt
      (fun p : ℝ × ℝ => z p.1 p.2) L
        (time s, ell s * r))
    (hJacobian : ∀ a c : ℝ,
      L (a,c) = (a : ℂ) * zt + (c : ℂ) * zr) :
    HasDerivAt
      (fun τ : ℝ =>
        rescalePhysicalRadiation (ell τ) (z (time τ)) r)
      ((((-(b s * ell s)) / (2 * Real.sqrt (ell s)) : ℝ) : ℂ) *
          z (time s) (ell s * r) +
        (Real.sqrt (ell s) : ℂ) *
          (((ell s) ^ 2 : ℝ) * zt +
            ((-(b s * ell s)) * r : ℝ) * zr)) s := by
  have h := actual_Hartree_physical_scale_clock_joint_time_jet
    ell time b z s r L hEll hEllPos hClock hJoint
  rw [hJacobian] at h
  simpa only [Algebra.smul_def, Complex.ofReal_mul] using h

end HBL.TypeIIDynamicSelection
