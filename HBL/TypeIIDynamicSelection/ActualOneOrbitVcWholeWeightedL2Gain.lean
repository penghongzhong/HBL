import HBL.TypeIIDynamicSelection.ActualOneOrbitVcWholeL2Gain
import HBL.WeightedPhaseAffineSource
import Mathlib.Tactic

/-!
# Quantitative genuine physical weighted Fredholm source bound

The exact real quartic density F_ell=|V_c+Z_ell|⁴-|V_c|⁴-|Z_ell|⁴,
with the moving moment-selected monopole and explicit terminal Hartree
radiation, has actual support [1/(4ell),4/ell]. Its previously proved
squared half-line L² mass is O(ell⁴).

On this true support the Japanese weight is controlled by its value
at 4/ell for sigma>=0; integrating gives the actual weighted source
bound needed for the H± Fredholm datum.

The mathematical rate for 3/2<sigma<2 is O(ell^(2-sigma))
in weighted L² norm. The present exact Lean bound keeps the physical
Japanese weight expression without a separate real-power asymptotic
lemma. It is only a terminal-time density estimate; original 2.12
still requires the true PDE projections and off-terminal matching.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.AffineTail HBL.Modulation.Monopole

/-- The whole genuine physical quartic cross-density has a quantitative
squared weighted source bound on its ACTUAL compact support. -/
theorem actual_one_orbit_Vc_whole_mixed_weighted_L2_square_le
    (ell sigma : ℝ) (hell : 0 < ell) (hsigma : 0 ≤ sigma) :
    (∫ r in Ioi (0 : ℝ),
      (affineJapaneseWeight sigma r *
        actualOneOrbitVcWholeMixedQuartic ell r) ^ 2) ≤
      (affineJapaneseWeight sigma (4 / ell)) ^ 2 *
        (∫ r in Ioi (0 : ℝ),
          |actualOneOrbitVcWholeMixedQuartic ell r| ^ 2) := by
  let F : ℝ → ℝ := actualOneOrbitVcWholeMixedQuartic ell
  let a : ℝ := 1 / (4 * ell)
  let b : ℝ := 4 / ell
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hFmeas : Measurable F :=
    actual_one_orbit_Vc_whole_mixed_measurable ell
  have hWmeas :
      AEStronglyMeasurable
        (fun r : ℝ => affineJapaneseWeight sigma r * F r)
        halfLineMeasure := by
    exact (((affineJapaneseWeight_continuous sigma).measurable).mul
      hFmeas).aestronglyMeasurable.restrict
  have hWmem : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r * F r) 2
      halfLineMeasure :=
    actual_one_orbit_Vc_whole_mixed_in_real_weighted_Fredholm
      ell sigma hell
  have hWsq : IntegrableOn
      (fun r : ℝ => (affineJapaneseWeight sigma r * F r) ^ 2)
      (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq hWmeas).1 hWmem
  have hFmem : MemLp F 2 halfLineMeasure := by
    simpa [InWeightedL2, affineJapaneseWeight] using
      (actual_one_orbit_Vc_whole_mixed_in_real_weighted_Fredholm
        ell 0 hell)
  have hFmeas' : AEStronglyMeasurable F halfLineMeasure :=
    hFmeas.aestronglyMeasurable.restrict
  have hFsq :
      IntegrableOn (fun r : ℝ => |F r| ^ 2)
        (Ioi (0 : ℝ)) := by
    have hInt : IntegrableOn (fun r : ℝ => F r ^ 2)
        (Ioi (0 : ℝ)) :=
      (memLp_two_iff_integrable_sq hFmeas').1 hFmem
    simpa only [sq_abs] using hInt
  have hSupport : Function.support F ⊆ Icc a b := by
    simpa only [F, a, b] using
      actual_one_orbit_Vc_whole_mixed_support ell hell
  have hWeight_nonneg (r : ℝ) :
      0 ≤ affineJapaneseWeight sigma r := by
    unfold affineJapaneseWeight
    positivity
  have hWeightBound (r : ℝ) (hr : r ∈ Icc a b) :
      affineJapaneseWeight sigma r ≤
        affineJapaneseWeight sigma b := by
    have hr0 : 0 ≤ r := (ha.trans_le hr.1).le
    have hbase : 1 + r ^ 2 ≤ 1 + b ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.2)
        (add_nonneg hr0 hb.le)]
    change (1 + r ^ 2) ^ (sigma / 2) ≤
      (1 + b ^ 2) ^ (sigma / 2)
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hPoint :
      ∀ᵐ r : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        (affineJapaneseWeight sigma r * F r) ^ 2 ≤
          (affineJapaneseWeight sigma b) ^ 2 * |F r| ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases hIn : r ∈ Icc a b
    · have hMul :
          |affineJapaneseWeight sigma r * F r| ≤
            affineJapaneseWeight sigma b * |F r| := by
        rw [abs_mul, abs_of_nonneg (hWeight_nonneg r)]
        exact mul_le_mul_of_nonneg_right
          (hWeightBound r hIn) (abs_nonneg _)
      have hSq := pow_le_pow_left₀ (abs_nonneg _) hMul 2
      simpa only [mul_pow, sq_abs] using hSq
    · have hZero : F r = 0 := by
        by_contra hn
        exact hIn (hSupport hn)
      simp [hZero]
  have hBound :
      (∫ r in Ioi (0 : ℝ),
        (affineJapaneseWeight sigma r * F r) ^ 2) ≤
        (affineJapaneseWeight sigma b) ^ 2 *
          (∫ r in Ioi (0 : ℝ), |F r| ^ 2) := by
    calc
      _ ≤ ∫ r in Ioi (0 : ℝ),
          (affineJapaneseWeight sigma b) ^ 2 * |F r| ^ 2 :=
        integral_mono_ae hWsq
          (hFsq.const_mul _) hPoint
      _ = (affineJapaneseWeight sigma b) ^ 2 *
          (∫ r in Ioi (0 : ℝ), |F r| ^ 2) :=
        integral_const_mul
  exact hBound

/-- A proved weighted source squared-norm upper bound in terms of
the actual boundary Japanese weight; for 3/2<sigma<2 it displays
the positive exponent 4-2sigma after elementary real-power
simplification. No time-dependent radiation localization is assumed. -/
theorem actual_one_orbit_Vc_whole_mixed_weighted_L2_fourth_order
    (ell sigma : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1)
    (hsigma : 0 ≤ sigma) :
    (∫ r in Ioi (0 : ℝ),
      (affineJapaneseWeight sigma r *
        actualOneOrbitVcWholeMixedQuartic ell r) ^ 2) ≤
      (affineJapaneseWeight sigma (4 / ell)) ^ 2 *
        ((actualOneOrbitVcWholeMixedL2Coefficient *
          actualOneOrbitVcWholeMixedHalfOrderCoefficient) *
            ell ^ 4) := by
  have hBound :=
    actual_one_orbit_Vc_whole_mixed_weighted_L2_square_le
      ell sigma hell hsigma
  have hL2 :=
    actual_one_orbit_Vc_whole_mixed_L2_square_fourth_order
      ell hell hsmall
  have hw : 0 ≤ (affineJapaneseWeight sigma (4 / ell)) ^ 2 :=
    sq_nonneg _
  exact hBound.trans (mul_le_mul_of_nonneg_left hL2 hw)

end HBL.TypeIIDynamicSelection
