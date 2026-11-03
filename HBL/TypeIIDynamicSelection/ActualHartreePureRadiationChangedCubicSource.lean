import HBL.TypeIIDynamicSelection.ActualHartreePureRadiationRieszLengthGain
import HBL.TypeIIDynamicSelection.ActualHartreeComplexCubicLipschitz
import Mathlib.Tactic

/-!
# HBL revised 2.13: real pure-radiation Hartree potential multiplies
# the ACTUAL changed complex cubic of the same physical field

Let V_c be the real moment-selected moving monopole and
Z_ell=sqrt(ell) z(ell r) the genuine critically scaled regular
Hartree field. The physical source's second nonlinear product is
 P[|Z_ell|^4](r)*(C(V_c+Z_ell)-C(Z_ell)),
where C(u)=|u|^2 u is the ORIGINAL cubic multiplier.

By the previously strict accepted true inverse-square quartic Riesz
scale covariance and Strauss bound, the potential carries O(ell).
By the previously strict accepted complex cubic Lipschitz estimate,
the local factor has a real-core amplitude with its actual quadratic
weight. This result retains both the true NONLOCAL convolution and
the original cubic. It neither replaces Hartree by a local NLS term,
nor assumes any terminal blowup law or manufactured regional source.

This is a supporting exact source estimate, not all of revised 2.13.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- TRUE same-field nonlocal pure-radiation interaction with changed
physical Hartree cubic has an explicit O(ell) factor, uniformly in
r>0. The remaining factor is the exact real-core/radiation
quadratic Lipschitz weight, not an independently imposed source. -/
theorem actual_Hartree_pure_radiation_changed_cubic_source_gain
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hr : 0 < r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let V : ℝ → ℝ :=
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
    let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
    let P : ℝ := radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r
    ‖(P : ℂ) *
      (actualWholeRadiationLocalCubic
        (fun x => (V x : ℂ) + Z x) r -
       actualWholeRadiationLocalCubic Z r)‖ ≤
      (radialHartreeRowBoundConstant *
        (2 * (B ^ 4 + A ^ 4))) * ell *
      ((‖(V r : ℂ) + Z r‖ + ‖Z r‖) ^ 2 * |V r|) := by
  dsimp only
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let P : ℝ := radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r
  let D : ℝ :=
    radialHartreeRowBoundConstant * (2 * (B ^ 4 + A ^ 4))
  let Q : ℝ := (‖(V r : ℂ) + Z r‖ + ‖Z r‖) ^ 2 * |V r|
  have hP : |P| ≤ D * ell := by
    simpa only [P,Z,D] using
      (actual_Hartree_pure_radiation_Riesz_uniform_length_gain
        ell r B A hell hr hB hA z hz hSup hStrauss)
  have hC : ‖actualWholeRadiationLocalCubic
      (fun x => (V x : ℂ) + Z x) r -
        actualWholeRadiationLocalCubic Z r‖ ≤ Q := by
    change ‖actualHartreeComplexCubic ((V r : ℂ) + Z r) -
      actualHartreeComplexCubic (Z r)‖ ≤ Q
    exact actual_Hartree_cubic_full_minus_radiation_bound (V r) (Z r)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  change ‖(P : ℂ) *
      (actualWholeRadiationLocalCubic
        (fun x => (V x : ℂ) + Z x) r -
       actualWholeRadiationLocalCubic Z r)‖ ≤
    D * ell * Q
  calc
    ‖(P : ℂ) *
        (actualWholeRadiationLocalCubic
          (fun x => (V x : ℂ) + Z x) r -
         actualWholeRadiationLocalCubic Z r)‖ =
      |P| * ‖actualWholeRadiationLocalCubic
        (fun x => (V x : ℂ) + Z x) r -
        actualWholeRadiationLocalCubic Z r‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |P| * Q :=
      mul_le_mul_of_nonneg_left hC (abs_nonneg P)
    _ ≤ (D * ell) * Q :=
      mul_le_mul_of_nonneg_right hP hQ
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
