import HBL.TypeIIDynamicSelection.ActualHartreePhysicalNonlocalSharpGain
import Mathlib.Tactic

/-!
# Strauss 1977 radial lemma supplies the genuine Hartree quartic Riesz envelope

W. A. Strauss, "Existence of solitary waves in higher dimensions",
Commun. Math. Phys. 55 (1977), 149--162,
DOI 10.1007/BF01626517, proves the classical radial Sobolev
pointwise decay. In 3D, radial H^1 has the standard bound
    r*|z(r)| <= C_Str * ||z||_{H^1}.

With the high-regularity Hartree LWP flow's uniform L-infinity bound,
the two quantitative inputs imply, by an IN-LEAN algebraic proof,
    |z(r)|^4 <= 2*(B^4 + A^4)*bubble(r)^2,
for ALL r>0. In particular the FULL inverse-square Hartree
cutoff Riesz commutator bound can be specialized without postulating
an independent quartic tail.

The precise Sobolev-to-continuous radial representative, the Strauss
norm constant, and the high-regularity solution bound remain explicit
EXTERNAL analytical interfaces. They are not new Lean axioms and they
do not imply the Type-II blowup rate or the full original HBL 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Elementary 3D Strauss-plus-L-infinity consequence: true quartic
Riesz density has the exact bubble-squared envelope needed by the
physical nonlocal Hartree source. No tail envelope is assumed. -/
theorem actual_Hartree_radial_quartic_envelope_from_Strauss
    (z : ℝ → ℂ) (B A : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSup : ∀ r : ℝ, 0 < r → ‖z r‖ ≤ B)
    (hStrauss : ∀ r : ℝ, 1 ≤ r → r * ‖z r‖ ≤ A) :
    ∀ r : ℝ, 0 < r →
      ‖z r‖ ^ 4 ≤ (2 * (B ^ 4 + A ^ 4)) * bubble r ^ 2 := by
  intro r hr
  have hd : 0 < 1 + r ^ 2 := by positivity
  have hw : bubble r ^ 2 = (1 + r ^ 2)⁻¹ := by
    unfold bubble
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [hw, ← div_eq_mul_inv]
  apply (le_div_iff₀ hd).2
  by_cases hsmall : r ≤ 1
  · have hfour : ‖z r‖ ^ 4 ≤ B ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (hSup r hr) 4
    have hsquare : r ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hsmall)]
    have hgeom : 1 + r ^ 2 ≤ 2 := by linarith
    calc
      ‖z r‖ ^ 4 * (1 + r ^ 2) ≤ B ^ 4 * (1 + r ^ 2) :=
        mul_le_mul_of_nonneg_right hfour hd.le
      _ ≤ B ^ 4 * 2 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ ≤ 2 * (B ^ 4 + A ^ 4) := by nlinarith [pow_nonneg A 4]
  · have hbig : 1 ≤ r := le_of_not_ge hsmall
    have hrad : r * ‖z r‖ ≤ A := hStrauss r hbig
    have hfour : (r * ‖z r‖) ^ 4 ≤ A ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg hr.le (norm_nonneg _)) hrad 4
    have hr2 : 1 ≤ r ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbig) (by positivity : 0 ≤ r + 1)]
    have hr4 : r ^ 2 ≤ r ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (sub_nonneg.mpr hr2))
        (sq_nonneg r)]
    have hgeom : 1 + r ^ 2 ≤ 2 * r ^ 4 := by nlinarith
    calc
      ‖z r‖ ^ 4 * (1 + r ^ 2) ≤ ‖z r‖ ^ 4 * (2 * r ^ 4) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 2 * (r * ‖z r‖) ^ 4 := by ring
      _ ≤ 2 * A ^ 4 := mul_le_mul_of_nonneg_left hfour (by norm_num)
      _ ≤ 2 * (B ^ 4 + A ^ 4) := by nlinarith [pow_nonneg B 4]

/-- The TRUE nonlocal inverse-square quartic Hartree cutoff source
gains all 5/2 critical powers from ordinary radial H1/Strichartz
bounds, without a separate quartic-envelope input. -/
theorem actual_Hartree_physical_nonlocal_sharp_from_Strauss
    (ell R r B A : ℝ)
    (hell : 0 < ell) (hR : 0 < R) (hr : 0 < r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    ‖complexRadialHartreeNonlinearity
        (fun x => actualOneLayerInnerOverlapCutoff R x *
          rescalePhysicalRadiation ell z x) r -
      actualOneLayerInnerOverlapCutoff R r *
        complexRadialHartreeNonlinearity
          (rescalePhysicalRadiation ell z) r‖ ≤
      (2 * radialHartreeRowBoundConstant *
        (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
        ell ^ 2 * Real.sqrt ell := by
  have hD : 0 ≤ 2 * (B ^ 4 + A ^ 4) := by positivity
  exact actual_Hartree_physical_nonlocal_cutoff_sharp_length_gain
    ell R r B (2 * (B ^ 4 + A ^ 4))
    hell hR hr hD hB z hz hSup
    (actual_Hartree_radial_quartic_envelope_from_Strauss
      z B A hB hA hSup hStrauss)

end HBL.TypeIIDynamicSelection
