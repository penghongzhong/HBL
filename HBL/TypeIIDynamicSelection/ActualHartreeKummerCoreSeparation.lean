import HBL.TypeIIDynamicSelection.ActualHartreeKummerCanonicalLocalizedSource
import HBL.TypeIIDynamicSelection.ActualHartreeMomentRadiusWindow
import Mathlib.Tactic

/-!
# Original 2.12: exact local Kummer Green equation inside physical Hartree cutoff

The canonical *fixed physical annulus* of the verified normalized Kummer
right inverse and the large physical moment-selected moving cutoff shell
need not overlap. This lemma proves their exact geometric separation
when the genuine physical concentration length is sufficiently small,
using the positive bounded quartic physical Hartree moment.

In that regime chi_R=1 and its first TWO derivatives vanish on the
Kummer annulus. Thus the REAL two-Wronskian-normalized inhomogeneous
Kummer Green solution obeys the ORIGINAL frozen differential equation
there with ZERO cutoff commutator, and no artificial C1 matching.

This does NOT supply Kummer large-radius asymptotics, global matching
or the missing physical mixed-source classes of original 2.12.
No Type-II rate, generated source order, or new axiom is postulated.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The genuine Kummer Green equation remains exact on an annulus
strictly inside the physical moving cutoff: all the DIFFERENTIAL
cutoff commutator terms vanish. -/
theorem actual_Hartree_normalized_Kummer_inside_physical_cutoff_exact
    {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (R : ℝ) (hR : 0 < R) (hRlarge : z + d ≤ R)
    (r : ℝ) (hr : r ∈ Ioo (z - d) (z + d)) :
    let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
    actualOneLayerInnerOverlapCutoff R r = 1 ∧
    deriv (actualOneLayerInnerOverlapCutoff R) r = 0 ∧
    deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r = 0 ∧
    actualHartreeFrozenKummerRadialApply mu theta
      (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r = F r := by
  dsimp only
  let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
  have hrR : r < R := hr.2.trans_le hRlarge
  have hsmall : r / R < 1 := (div_lt_iff₀ hR).2 (by simpa using hrR)
  have hCut : cutoff (r / R) = 0 :=
    cutoff_zero_of_le_one (r / R) hsmall.le
  have hFirstCut : deriv cutoff (r / R) = 0 :=
    cutoff_deriv_zero_of_lt_one hsmall
  have hSecondCut : deriv (deriv cutoff) (r / R) = 0 :=
    actual_fixed_Hartree_overlap_cutoff_second_deriv_zero_left hsmall
  have hChi : actualOneLayerInnerOverlapCutoff R r = 1 := by
    simp only [actualOneLayerInnerOverlapCutoff, hCut, sub_zero,
      Complex.ofReal_one]
  have hdChi : deriv (actualOneLayerInnerOverlapCutoff R) r = 0 := by
    rw [(actual_one_layer_overlap_cutoff_hasDerivAt R r).deriv,
      hFirstCut]
    norm_num
  have hddChi : deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r = 0 := by
    rw [(actual_one_layer_overlap_cutoff_deriv_hasDerivAt R r hR.ne').deriv,
      hSecondCut]
    norm_num
  have hODE :=
    actual_Hartree_original_normalized_Kummer_localized_source_exact
      K d hd hde F hF R hR.ne' r hr
  dsimp only at hODE
  rw [hChi, hdChi, hddChi] at hODE
  simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul, sub_eq_zero] at hODE
  exact ⟨hChi, hdChi, hddChi, hODE⟩

/-- The true radial inverse-square Hartree quartic moment, if bounded
above along the selected regular radiation orbit, makes the original
physical cutoff radius exceed any prescribed fixed Kummer annulus
for all sufficiently small positive concentration lengths. -/
theorem actual_Hartree_moment_cutoff_covers_Kummer_annulus
    (ell m M z d : ℝ)
    (hell : 0 < ell) (hm : 0 < m) (hmBound : m ≤ M)
    (hz : 0 < z + d)
    (hellSmall : ell ≤ 4 / (hartreeKappa * M * (z + d))) :
    z + d ≤ actualHartreeMomentCutoffRadius ell m := by
  have hM : 0 < M := lt_of_lt_of_le hm hmBound
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hden0 : 0 < hartreeKappa * M * (z + d) := by positivity
  have hsmallProduct :
      (hartreeKappa * M * (z + d)) * ell ≤ 4 := by
    calc
      (hartreeKappa * M * (z + d)) * ell =
          ell * (hartreeKappa * M * (z + d)) := by ring
      _ ≤ 4 := (le_div_iff₀ hden0).mp hellSmall
  have hProduct :
      (hartreeKappa * ell * m) * (z + d) ≤ 4 := by
    calc
      (hartreeKappa * ell * m) * (z + d) =
          (hartreeKappa * ell * (z + d)) * m := by ring
      _ ≤ (hartreeKappa * ell * (z + d)) * M :=
        mul_le_mul_of_nonneg_left hmBound (by positivity)
      _ = (hartreeKappa * M * (z + d)) * ell := by ring
      _ ≤ 4 := hsmallProduct
  have hden : 0 < hartreeKappa * ell * m := by positivity
  have hRescaled :
      z + d ≤ 4 / (hartreeKappa * ell * m) := by
    apply (le_div_iff₀ hden).2
    calc
      (z + d) * (hartreeKappa * ell * m) =
          (hartreeKappa * ell * m) * (z + d) := by ring
      _ ≤ 4 := hProduct
  exact hRescaled

/-- Exact source-preserving regional Kummer parametrix on a fixed
annulus with the *real* physical Hartree-moment cutoff radius
R=4/(kappa_H*ell*m). No arbitrary interface jet or smallness rate
is inserted, merely the explicitly quantified finite moment bound. -/
theorem actual_Hartree_moment_selected_Kummer_annulus_source_exact
    {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (ell m M : ℝ)
    (hell : 0 < ell) (hm : 0 < m) (hmBound : m ≤ M)
    (hz : 0 < z + d)
    (hellSmall : ell ≤ 4 / (hartreeKappa * M * (z + d)))
    (r : ℝ) (hr : r ∈ Ioo (z - d) (z + d)) :
    let R := actualHartreeMomentCutoffRadius ell m
    let u := actualKummerCauchyValue K d F 0 0
    actualHartreeFrozenKummerRadialApply mu theta
      (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r = F r := by
  dsimp only
  have hRlarge :=
    actual_Hartree_moment_cutoff_covers_Kummer_annulus
      ell m M z d hell hm hmBound hz hellSmall
  have hR : 0 < actualHartreeMomentCutoffRadius ell m :=
    (actual_Hartree_real_moment_radius_inverse_le
      ell m M hell hm hmBound).1
  exact (actual_Hartree_normalized_Kummer_inside_physical_cutoff_exact
    K d hd hde F hF (actualHartreeMomentCutoffRadius ell m)
    hR hRlarge r hr).2.2.2

end HBL.TypeIIDynamicSelection
