import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Two-stage ACTUAL energy-critical Hartree radiation time derivative

The physical complex radiation in the same critically rescaled
Hartree source is not an abstract source profile:
  Z_a,ell(t,r)=sqrt(a(t))*sqrt(ell(t))*z(t,ell(t)*a(t)*r).

This theorem derives its full time tangent from:
- the actual scale paths a(t),ell(t) and their derivatives;
- a single physical C1 differential for the ORIGINAL complex
  radiation map (t,rho)↦z(t,rho).

It includes every factor and the physical moving argument,
with no preselected Type-II rate or independent derivative of
the scaled radiation. The original Hartree local flow must still
supply the actual full C1 radiation differential on its orbit.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_two_stage_critical_radiation_time_hasDerivAt
    (a ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (s r adot ellDot : ℝ)
    (ha : HasDerivAt a adot s)
    (hEll : HasDerivAt ell ellDot s)
    (hapos : 0 < a s) (hellpos : 0 < ell s)
    (D : (ℝ × ℝ) →L[ℝ] ℂ)
    (hZ : HasFDerivAt
      (fun p : ℝ × ℝ => z p.1 p.2) D
      (s, ell s * (a s * r))) :
    HasDerivAt
      (fun t => rescalePhysicalRadiation (a t)
        (rescalePhysicalRadiation (ell t) (z t)) r)
      (((adot / (2 * Real.sqrt (a s)) : ℝ) : ℂ) *
          (Real.sqrt (ell s) : ℂ) *
          z s (ell s * (a s * r)) +
        (Real.sqrt (a s) : ℂ) *
          (((ellDot / (2 * Real.sqrt (ell s)) : ℝ) : ℂ)) *
          z s (ell s * (a s * r)) +
        (Real.sqrt (a s) : ℂ) * (Real.sqrt (ell s) : ℂ) *
          D (1, ellDot * (a s * r) + ell s * (adot * r))) s := by
  let x : ℝ → ℝ := fun t => ell t * (a t * r)
  have hAR : HasDerivAt (fun t => a t * r) (adot * r) s :=
    ha.mul_const r
  have hX : HasDerivAt x
      (ellDot * (a s * r) + ell s * (adot * r)) s := by
    convert hEll.mul hAR using 1
  have hXPair : HasDerivAt (fun t => (t, x t))
      (1, ellDot * (a s * r) + ell s * (adot * r)) s :=
    (hasDerivAt_id s).prodMk hX
  have hRadiation :=
    hZ.comp_hasDerivAt s hXPair
  have hAroot : HasDerivAt (fun t => Real.sqrt (a t))
      (adot / (2 * Real.sqrt (a s))) s := ha.sqrt hapos.ne'
  have hEllroot : HasDerivAt (fun t => Real.sqrt (ell t))
      (ellDot / (2 * Real.sqrt (ell s))) s := hEll.sqrt hellpos.ne'
  have hRoot : HasDerivAt
      (fun t => Real.sqrt (a t) * Real.sqrt (ell t))
      (adot / (2 * Real.sqrt (a s)) * Real.sqrt (ell s) +
        Real.sqrt (a s) * (ellDot / (2 * Real.sqrt (ell s)))) s := by
    convert hAroot.mul hEllroot using 1
  have hRootC := hRoot.ofReal_comp
  have hTotal := hRootC.mul hRadiation
  convert hTotal using 1
  · funext t
    dsimp [rescalePhysicalRadiation, x]
    push_cast
    ring
  · dsimp only [Function.comp_apply, x]
    push_cast
    ring

end HBL.TypeIIDynamicSelection
