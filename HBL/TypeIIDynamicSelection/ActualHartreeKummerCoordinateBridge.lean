import HBL.TypeIIDynamicSelection.ActualHartreeKummerCoreSeparation
import Mathlib.Tactic

/-!
# Original HBL 2.12: the ACTUAL physical-to-Kummer change of radius

The self-similar Kummer ODE uses z = R_bubble / sqrt(q), where
q=(T-t)*lambda^2 >0; the radiation moving cutoff is in the
bubble coordinate R_bubble. One MUST NOT put the bubble
moving radius directly into the Kummer ODE as a z-radius.

This module implements the EXACT geometry:
  chi_(R_phys)(sqrt(q)*z) = chi_(R_z)(z),
  R_phys = 4/(kappa_H * ell * m),
  R_z = 4/(kappa_H * ell * sqrt(q) * m).

The condition that the genuine Kummer annulus is inside the
original physical cutoff is ell*sqrt(q) sufficiently small,
NOT ell alone. This is consistent with (but does not assume
asymptotic equality to) the PDE-derived trapping beta>1/2.

The actual Hartree moment is still the genuine inverse-square
quartic 3D moment, bounded by the true selected radiation
flow. No Type-II limiting rate or generated-order cancellation
is inserted. Source-to-jet and all global matching still remain.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The one-orbit moment-selected physical cutoff expressed
in the true Kummer self-similar variable z. -/
def actualHartreeKummerCoordinateCutoffRadius
    (ell q m : ℝ) : ℝ :=
  actualHartreeMomentCutoffRadius (ell * Real.sqrt q) m

/-- Exact coordinate conversion of the fixed original smooth cutoff.
This statement is independent of the Hartree PDE and has no
approximate or asymptotic coordinate substitution. -/
theorem actual_Hartree_cutoff_coordinate_rescale
    (a k r : ℝ) (ha : 0 < a) (hk : 0 < k) :
    actualOneLayerInnerOverlapCutoff a (k * r) =
      actualOneLayerInnerOverlapCutoff (a / k) r := by
  have hRatio : (k * r) / a = r / (a / k) := by
    field_simp [ha.ne', hk.ne']
  unfold actualOneLayerInnerOverlapCutoff
  rw [hRatio]

/-- The genuine physical moment R=4/(kappa_H*ell*m)
is transformed into the Kummer-coordinate cutoff with
the correct factor sqrt(q), not identified by fiat. -/
theorem actual_Hartree_physical_Kummer_cutoff_coordinate_exact
    (ell q m r : ℝ) (hell : 0 < ell) (hq : 0 < q) (hm : 0 < m) :
    actualOneLayerInnerOverlapCutoff
      (actualHartreeMomentCutoffRadius ell m) (Real.sqrt q * r) =
    actualOneLayerInnerOverlapCutoff
      (actualHartreeKummerCoordinateCutoffRadius ell q m) r := by
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hR : 0 < actualHartreeMomentCutoffRadius ell m := by
    dsimp [actualHartreeMomentCutoffRadius]
    positivity
  have hCoord :
      actualHartreeKummerCoordinateCutoffRadius ell q m =
        actualHartreeMomentCutoffRadius ell m / Real.sqrt q := by
    dsimp [actualHartreeKummerCoordinateCutoffRadius,
      actualHartreeMomentCutoffRadius]
    field_simp [hk.ne', hell.ne', hm.ne', hs.ne']
  rw [hCoord]
  exact actual_Hartree_cutoff_coordinate_rescale
    (actualHartreeMomentCutoffRadius ell m) (Real.sqrt q) r hR hs

/-- Correct geometry for the actual manuscript's
prescribed fixed Kummer annulus under the physical Hartree moment
cutoff. Unlike a SAME-COORDINATE surrogate, this includes sqrt(q). -/
theorem actual_Hartree_Kummer_coordinate_moment_annulus_covered
    (ell q m M center d : ℝ)
    (hell : 0 < ell) (hq : 0 < q) (hm : 0 < m)
    (hmBound : m ≤ M) (hcenter : 0 < center + d)
    (hSmall : ell * Real.sqrt q ≤
      4 / (hartreeKappa * M * (center + d))) :
    center + d ≤ actualHartreeKummerCoordinateCutoffRadius ell q m := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hR := actual_Hartree_moment_cutoff_covers_Kummer_annulus
    (ell * Real.sqrt q) m M center d
    (mul_pos hell hs) hm hmBound hcenter hSmall
  exact hR

/-- Genuine Kummer-radius localized canonical Green source equation,
with the physical moment-selected cutoff transformed through
R_bubble = sqrt(q)*z. The original Kummer normalization is untouched.
This still does NOT provide any global nonlocal Hartree gluing. -/
theorem actual_Hartree_Kummer_coordinate_original_source_exact
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (ell q m M : ℝ)
    (hell : 0 < ell) (hq : 0 < q)
    (hm : 0 < m) (hmBound : m ≤ M)
    (hcenter : 0 < center + d)
    (hSmall : ell * Real.sqrt q ≤
      4 / (hartreeKappa * M * (center + d)))
    (r : ℝ) (hr : r ∈ Ioo (center - d) (center + d)) :
    let Rz := actualHartreeKummerCoordinateCutoffRadius ell q m
    actualHartreeFrozenKummerRadialApply mu theta
      (fun x => actualOneLayerInnerOverlapCutoff Rz x *
        actualKummerCauchyValue K d F 0 0 x) r = F r := by
  dsimp only
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hRadius : 0 < actualHartreeKummerCoordinateCutoffRadius ell q m := by
    dsimp [actualHartreeKummerCoordinateCutoffRadius]
    exact (actual_Hartree_real_moment_radius_inverse_le
      (ell * Real.sqrt q) m M (mul_pos hell hs) hm hmBound).1
  have hAbove :=
    actual_Hartree_Kummer_coordinate_moment_annulus_covered
      ell q m M center d hell hq hm hmBound hcenter hSmall
  exact (actual_Hartree_normalized_Kummer_inside_physical_cutoff_exact
      K d hd hde F hF
      (actualHartreeKummerCoordinateCutoffRadius ell q m)
      hRadius hAbove r hr).2.2.2

end HBL.TypeIIDynamicSelection
