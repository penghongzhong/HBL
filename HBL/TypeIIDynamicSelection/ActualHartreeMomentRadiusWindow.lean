import HBL.TypeIIDynamicSelection.ActualHartreeMomentSpatialStrictGain
import Mathlib.Tactic

/-!
# Actual physical Hartree quartic moment fixes the moving cutoff radius

For a single real Hartree trajectory with m0 <= m(t) <= M,
the original radius is R=4/(kappa_H*ell*m(t)). Its upper bound
R<=4/(kappa_H*m0*ell) is DEDUCED from positive physical terminal
moment, not a freely prescribed radius, and converts the real
moving overlap into one fixed physical-radius observation interval.

This is required for replacing the large shell's weighted L2 loss
by the genuine 5/2 critical source gain. No terminal blowup rate
is assumed or obtained by this lemma.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail

/-- A positive lower bound on the actual physical quartic moment
gives an upper moving cutoff radius for every ell>0. -/
theorem actual_Hartree_positive_moment_upper_cutoff_radius
    (ell m m0 : ℝ)
    (hell : 0 < ell) (hm0 : 0 < m0) (hmin : m0 ≤ m) :
    actualHartreeMomentCutoffRadius ell m ≤
      (4 / (hartreeKappa * m0)) / ell := by
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hm : 0 < m := hm0.trans_le hmin
  have hden : 0 < hartreeKappa * ell * m := by positivity
  have hden0 : 0 < hartreeKappa * ell * m0 := by positivity
  have hprod :
      hartreeKappa * ell * m0 ≤ hartreeKappa * ell * m :=
    mul_le_mul_of_nonneg_left hmin (by positivity)
  have hfrac :
      4 / (hartreeKappa * ell * m) ≤
        4 / (hartreeKappa * ell * m0) := by
    apply (div_le_div_iff₀ hden hden0).2
    nlinarith [hprod]
  unfold actualHartreeMomentCutoffRadius
  calc
    4 / (hartreeKappa * ell * m) ≤
        4 / (hartreeKappa * ell * m0) := hfrac
    _ = (4 / (hartreeKappa * m0)) / ell := by
      field_simp [hell.ne', hk.ne', hm0.ne']

/-- The ACTUAL moving Hartree overlap r<=2R is contained
in a fixed physical radius after critical rescaling. -/
theorem actual_Hartree_moving_overlap_rescaled_radius_le
    (ell m m0 r : ℝ)
    (hell : 0 < ell) (hm0 : 0 < m0) (hmin : m0 ≤ m)
    (hr : r ≤ 2 * actualHartreeMomentCutoffRadius ell m) :
    ell * r ≤ 8 / (hartreeKappa * m0) := by
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hR := actual_Hartree_positive_moment_upper_cutoff_radius
    ell m m0 hell hm0 hmin
  calc
    ell * r ≤ ell * (2 * actualHartreeMomentCutoffRadius ell m) :=
      mul_le_mul_of_nonneg_left hr hell.le
    _ ≤ ell * (2 * ((4 / (hartreeKappa * m0)) / ell)) := by
      have htwice :
          2 * actualHartreeMomentCutoffRadius ell m ≤
            2 * ((4 / (hartreeKappa * m0)) / ell) :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
      exact mul_le_mul_of_nonneg_left htwice hell.le
    _ = 8 / (hartreeKappa * m0) := by
      field_simp [hell.ne', hk.ne', hm0.ne']

end HBL.TypeIIDynamicSelection
