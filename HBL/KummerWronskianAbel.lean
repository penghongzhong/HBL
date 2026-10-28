import HBL.KummerVariationOfParameters
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Abel identity for the Kummer Wronskian

This file removes the Wronskian differential identity from the list of
analytic inputs.  For any genuine C2 fundamental pair satisfying the same
second-order equation, Lean proves
  W' = -a W.
The nonvanishing consequence is handled in the subsequent normalized
annulus construction.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.Kummer

theorem wronskian_hasDerivAt
    (K : FundamentalPair) (z : ℝ) :
    HasDerivAt (wronskian K)
      (-(K.a z) * wronskian K z) z := by
  have hprod1 :=
    (K.phi_hasDeriv z).mul (K.dpsi_hasDeriv z)
  have hprod2 :=
    (K.dphi_hasDeriv z).mul (K.psi_hasDeriv z)
  have h := hprod1.sub hprod2
  convert h using 1
  · rfl
  · unfold wronskian
    have hphi := K.phi_homogeneous z
    have hpsi := K.psi_homogeneous z
    linear_combination
      (K.phi z) * hpsi - (K.psi z) * hphi

theorem wronskian_deriv
    (K : FundamentalPair) (z : ℝ) :
    deriv (wronskian K) z =
      -(K.a z) * wronskian K z :=
  (wronskian_hasDerivAt K z).deriv

theorem wronskian_differentiable
    (K : FundamentalPair) :
    Differentiable ℝ (wronskian K) := by
  intro z
  exact (wronskian_hasDerivAt K z).differentiableAt

#print axioms wronskian_hasDerivAt
#print axioms wronskian_deriv
#print axioms wronskian_differentiable

end HBL.Profile.Kummer
