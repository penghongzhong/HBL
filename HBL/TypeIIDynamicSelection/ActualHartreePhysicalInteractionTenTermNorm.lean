import HBL.TypeIIDynamicSelection.ActualHartreeFourComponentCubicControl
import HBL.TypeIIDynamicSelection.ActualHartreeFullInteractionSourceSplit
import Mathlib.Tactic

/-!
# Revised HBL 2.13 — true physical PDE Hartree interaction, exact ten-term norm bridge

Use ONE actual radial real core V, ONE complex radiation Z, and the
three original inverse-square radial Hartree Riesz potentials.
The already compiled exact four-term source identity is combined
with the independently audited universal complex cubic bound.
No Riesz source is replaced by an abstract placeholder; no Type-II
time rate, interfacial compatibility, source order or finite-profile
packet is assumed.

This is the true source-to-scalar bridge. Spatial potential estimates
and weighted L2 integration are separate downstream obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- All TEN monomials in the same original physical Hartree nonlocal
interaction, with genuine radial Riesz potentials and actual cubic. -/
def actualHartreePhysicalInteractionTenTermEnvelope
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (s r : ℝ) : ℝ :=
  let pm : ℝ := radialHartreePotential
    (actualWholeRadiationMixedQuartic (V s) (Z s)) r
  let pz : ℝ := radialHartreePotential
    (fun rho => ‖Z s rho‖ ^ 4) r
  let pc : ℝ := radialHartreePotential
    (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r
  let v : ℂ := V s r
  let z : ℂ := Z s r
  |pm| * (‖v‖ ^ 3 + (2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) +
    |pz| * ((‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖) +
    |pc| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖)

/-- The actual one-layer Hartree PDE interaction, not a formally
independent forcing, obeys the complete scalar ten-monomial envelope
with all three physical nonlocal Riesz potentials retained. -/
theorem actual_Hartree_physical_interaction_complete_ten_term_norm_le
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (s r : ℝ) :
    ‖actualOneLayerInteractionOnly V Z s r‖ ≤
      actualHartreePhysicalInteractionTenTermEnvelope V Z s r := by
  let pm : ℝ := radialHartreePotential
    (actualWholeRadiationMixedQuartic (V s) (Z s)) r
  let pz : ℝ := radialHartreePotential
    (fun rho => ‖Z s rho‖ ^ 4) r
  let pc : ℝ := radialHartreePotential
    (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r
  let v : ℂ := V s r
  let z : ℂ := Z s r
  have hCoreCubic :
      actualHartreeComplexCubic v = v ^ 3 := by
    have hC :=
      actual_Hartree_complex_cubic_is_same_PDE_factor
        (fun x : ℝ => (V s x : ℂ)) r
    have hReal := actual_Hartree_real_core_cubic_is_cube (V s) r
    exact hC.symm.trans hReal
  have hSplit0 :=
    actual_Hartree_complete_nonlinear_interaction_four_term_split
      V Z s r
  simp only [actual_Hartree_complex_cubic_is_same_PDE_factor]
    at hSplit0
  rw [← hCoreCubic] at hSplit0
  have hSplit :
      actualOneLayerInteractionOnly V Z s r =
        (pm : ℂ) * actualHartreeComplexCubic v +
        (pm : ℂ) *
          (actualHartreeComplexCubic (v + z) -
            actualHartreeComplexCubic v) +
        (pz : ℂ) *
          (actualHartreeComplexCubic (v + z) -
            actualHartreeComplexCubic z) +
        (pc : ℂ) *
          (actualHartreeComplexCubic (v + z) -
            actualHartreeComplexCubic v) := by
    simpa only [pm,pz,pc,v,z] using hSplit0
  rw [hSplit]
  change
    ‖(pm : ℂ) * actualHartreeComplexCubic v +
      (pm : ℂ) *
        (actualHartreeComplexCubic (v + z) -
          actualHartreeComplexCubic v) +
      (pz : ℂ) *
        (actualHartreeComplexCubic (v + z) -
          actualHartreeComplexCubic z) +
      (pc : ℂ) *
        (actualHartreeComplexCubic (v + z) -
          actualHartreeComplexCubic v)‖ ≤
      |pm| * (‖v‖ ^ 3 + (2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖) +
        |pz| * ((‖v‖ + 2 * ‖z‖) ^ 2 * ‖v‖) +
        |pc| * ((2 * ‖v‖ + ‖z‖) ^ 2 * ‖z‖)
  exact actual_Hartree_four_product_complete_cubic_norm_le
    v z pm pz pc

end HBL.TypeIIDynamicSelection
