import HBL.TypeIIDynamicSelection.ActualOneOrbitLinearMixedCenter
import HBL.RadialHartreeMultipole
import Mathlib.Tactic

/-!
# Exact core Hartree-Riesz potential of a selected physical linear mixed source

This connects the already strict-checked physical linear density
4 W^3 Re Z_ell to the ACTUAL (not model) radial inverse-square Hartree
convolution, using the selected annular smooth nonzero terminal datum.

For r in the separated inner core, the complete Riesz potential equals
its genuine exterior Riesz potential. The scalar center is the previously
proved O(ell^(5/2)) center, and the difference is controlled by the
spatially weighted |F|/rho^2 integral of the SAME source.

This is a strict original-PDE source component for manuscript 2.12,
NOT the full simultaneous physical two-threshold/Kummer/remote matching.
No time-decay exponent, prescribed rate, or abstract source inverse
is a theorem hypothesis.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- Localization identity for the entire half-line integral when the
true integrand vanishes on (0,a]. Uses no abstract source classification. -/
private theorem integral_Ioi_zero_if_vanishes_below
    (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ)
    (hzero : ∀ x : ℝ, 0 < x → x ≤ a → f x = 0) :
    (∫ x in Ioi (0 : ℝ), f x) = ∫ x in Ioi a, f x := by
  have hsubset : Ioi a ⊆ Ioi (0 : ℝ) :=
    fun x hx => ha.trans_lt hx
  calc
    (∫ x in Ioi (0 : ℝ), f x) =
      ∫ x in Ioi (0 : ℝ), (Ioi a).indicator f x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        by_cases hax : a < x
        · simp [Set.indicator_of_mem hax]
        · have hz : f x = 0 := hzero x hx (le_of_not_gt hax)
          simp [Set.indicator_of_notMem (show x ∉ Ioi a by exact hax), hz]
    _ = ∫ x in Ioi (0 : ℝ) ∩ Ioi a, f x :=
      setIntegral_indicator measurableSet_Ioi
    _ = ∫ x in Ioi a, f x := by rw [inter_eq_right.mpr hsubset]

/-- The actual selected physical real-linear quartic Hartree density
vanishes throughout the positive inner region before its physical
support annulus starts. -/
private theorem actual_one_orbit_linear_density_zero_below
    (ell : ℝ) (hell : 0 < ell)
    (x : ℝ) (hx : x ≤ 1 / (4 * ell)) :
    actualOneOrbitLinearMixedDensity ell x = 0 := by
  have hz := actual_one_orbit_rescaled_terminal_zero_core ell x hell hx
  simp [actualOneOrbitLinearMixedDensity, hz]

/-- The original *entire* linear Hartree center is exactly its
exterior center for a selected terminal datum, with no artificial
exterior-only replacement of the original source. -/
theorem actual_one_orbit_linear_mixed_center_eq_exterior
    (ell : ℝ) (hell : 0 < ell) :
    radialHartreeCenter (actualOneOrbitLinearMixedDensity ell) =
      radialHartreeExteriorCenter
        (actualOneOrbitLinearMixedDensity ell) (1 / (4 * ell)) := by
  have ha : 0 ≤ 1 / (4 * ell) := by positivity
  unfold radialHartreeCenter radialHartreeExteriorCenter
  rw [integral_Ioi_zero_if_vanishes_below
    (1 / (4 * ell)) ha (actualOneOrbitLinearMixedDensity ell)
    (fun x _ hx => actual_one_orbit_linear_density_zero_below ell hell x hx)]

/-- The TRUE physical full Hartree Riesz operator is exactly the
genuine exterior Riesz operator on the physical linear-density
source. This is an equality of integrals, not a source-assignment
hypothesis, valid for every positive observation radius. -/
theorem actual_one_orbit_linear_mixed_Riesz_eq_exterior
    (ell r : ℝ) (hell : 0 < ell) :
    radialHartreePotential (actualOneOrbitLinearMixedDensity ell) r =
      radialHartreeExteriorPotential
        (actualOneOrbitLinearMixedDensity ell) (1 / (4 * ell)) r := by
  let F := actualOneOrbitLinearMixedDensity ell
  let a := 1 / (4 * ell)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hzero : ∀ x : ℝ, 0 < x → x ≤ a →
      x * hartreeRadialLog r x * F x = 0 := by
    intro x _ hx
    have hz : F x = 0 := by
      exact actual_one_orbit_linear_density_zero_below ell hell x hx
    simp [hz]
  have hint := integral_Ioi_zero_if_vanishes_below a ha
    (fun x => x * hartreeRadialLog r x * F x) hzero
  unfold radialHartreePotential radialHartreeExteriorPotential
  rw [hint]

/-- On the actual separated bubble core, the genuine nonlocal
3D Hartree potential is a scalar charge plus an explicitly weighted
quadratic remainder. The source is the SAME full physical mixed
density and belongs to the actual Riesz row space, proved here. -/
theorem actual_one_orbit_linear_mixed_Riesz_core_center_error
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hsep : 2 * r ≤ 1 / (4 * ell)) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualOneOrbitLinearMixedDensity ell rho)
      (Ioi (0 : ℝ)) ∧
    |radialHartreePotential (actualOneOrbitLinearMixedDensity ell) r -
      radialHartreeCenter (actualOneOrbitLinearMixedDensity ell)| ≤
      4 * Real.pi * hartreeKappa * r ^ 2 *
        ∫ rho in Ioi (1 / (4 * ell)),
          |actualOneOrbitLinearMixedDensity ell rho| / rho ^ 2 := by
  let F := actualOneOrbitLinearMixedDensity ell
  let a := 1 / (4 * ell)
  have ha : 0 < a := by dsimp [a]; positivity
  have hf : Measurable F :=
    (actual_one_orbit_linear_mixed_density_continuous ell).measurable
  have hFint : IntegrableOn F (Ioi (0 : ℝ)) :=
    (actual_one_orbit_linear_mixed_Hartree_center_five_halves_gain ell hell).1
  have hFext : IntegrableOn F (Ioi a) :=
    hFint.mono_set (fun x hx => ha.trans hx)
  obtain ⟨_hweighted, hrow, herr⟩ :=
    radialHartreeExteriorPotential_quadratic_center F hf hFext ha hr hsep
  let G : ℝ → ℝ := fun rho => rho * hartreeRadialLog r rho * F rho
  have hnear : IntegrableOn G (Ioc (0 : ℝ) a) := by
    apply integrableOn_zero.congr_fun ?_ measurableSet_Ioc
    intro rho hρ
    change G rho = 0
    have hz := actual_one_orbit_linear_density_zero_below ell hell
      rho hρ.2
    simp [G, F, hz]
  have hfull : IntegrableOn G (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact hnear.union hrow
  refine ⟨hfull, ?_⟩
  rw [actual_one_orbit_linear_mixed_Riesz_eq_exterior ell r hell,
    actual_one_orbit_linear_mixed_center_eq_exterior ell hell]
  exact herr

end HBL.TypeIIDynamicSelection
