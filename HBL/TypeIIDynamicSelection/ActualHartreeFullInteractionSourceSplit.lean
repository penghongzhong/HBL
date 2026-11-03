import HBL.TypeIIDynamicSelection.ActualHartreeComplexCubicLipschitz
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import Mathlib.Tactic

/-!
# HBL revised 2.13: exact full Hartree interaction split into the
# already controlled mixed-Riesz x core-cubic and three real remainders

The original energy-critical generalized Hartree nonlinearity is
N(u)=I[|u|^4] |u|^2 u. For a real concentrating core V and complex
regular radiation Z, the same physical PDE interaction is split as

 P_mix C(V) +
 P_mix (C(V+Z)-C(V)) +
 P_Z (C(V+Z)-C(Z)) +
 P_V (C(V+Z)-C(V)).

No Hartree term is discarded, and C(V)=V^3 is proved directly from
the genuine complex norm. This explicit splitting isolates the
component whose original weighted-L2 positive order was STRICTLY
accepted in the preceding quantitative Riesz bridge. The other
three terms and actual finite-profile cancellation remain OPEN.
No independently prescribed source or Type-II rate appears.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original complex Hartree local cubic of the SAME real
physical monopole field is exactly the real cubic under embedding. -/
theorem actual_Hartree_real_core_cubic_is_cube
    (V : ℝ → ℝ) (r : ℝ) :
    actualWholeRadiationLocalCubic (fun x => (V x : ℂ)) r =
      (V r : ℂ) ^ 3 := by
  unfold actualWholeRadiationLocalCubic
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

/-- The exact full three-product Hartree source splits into the
already verified mixed-quartic-Riesz times original real core cubic
and the three remaining physically generated interactions.
This is an equality on the SAME physical density and kernel,
not the introduction of four independent regional forcing sources. -/
theorem actual_Hartree_complete_nonlinear_interaction_four_term_split
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (s r : ℝ) :
    actualOneLayerInteractionOnly V Z s r =
      (radialHartreePotential
        (actualWholeRadiationMixedQuartic (V s) (Z s)) r : ℂ) *
        (V s r : ℂ) ^ 3 +
      (radialHartreePotential
        (actualWholeRadiationMixedQuartic (V s) (Z s)) r : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun x => (V s x : ℂ) + Z s x) r -
         actualWholeRadiationLocalCubic
           (fun x => (V s x : ℂ)) r) +
      (radialHartreePotential (fun rho => ‖Z s rho‖ ^ 4) r : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun x => (V s x : ℂ) + Z s x) r -
         actualWholeRadiationLocalCubic (Z s) r) +
      (radialHartreePotential
        (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun x => (V s x : ℂ) + Z s x) r -
         actualWholeRadiationLocalCubic
           (fun x => (V s x : ℂ)) r) := by
  have hCore := actual_Hartree_real_core_cubic_is_cube (V s) r
  unfold actualOneLayerInteractionOnly
  rw [hCore]
  ring

end HBL.TypeIIDynamicSelection
