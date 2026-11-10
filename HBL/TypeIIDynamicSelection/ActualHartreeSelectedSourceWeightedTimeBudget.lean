import HBL.TypeIIDynamicSelection.ActualHartreeMovingSelectedSourceTimeBudget
import Mathlib.Tactic

/-!
# The physical Cramer-selected Hartree source time derivative in radius-weighted form

The SAME genuine quartic Riesz forcing, moving two real compatibility
columns and two true modulation source directions enter the earlier
strict source-time budget. Its pointwise estimate contains precisely
one inverse observation-radius power. Multiplying by the physical
positive observation radius cancels this factor algebraically, without
postulating an independent differentiated source, a Type-II rate,
or an artificial Green-region envelope.

The remaining primitive source and compatibility derivatives still
require quantitative control along the constructed PDE orbit.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual selected physical Hartree source derivative with no hidden
inverse *left endpoint*: after multiplication by r, its two-speed
Cramer derivative cost has no inverse radius. This is not, by itself,
the necessary final *time decay* estimate for the four-region PDE. -/
theorem actual_Hartree_true_moving_selected_source_radius_weighted_time_budget
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s r L B : ℝ)
    (hL : 1 ≤ L) (ha : 0 < a s) (hB : 0 < B) (hBOne : B ≤ 1)
    (hSmall : a s * |c s| ≤ 1)
    (hr : r ∈ Icc (L / a s) B)
    (bdot wdot Zdot Fdot Sdot Pdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hbNorm : ‖b s‖ ≤ a s * B ^ 2)
    (hwNorm : ‖w s‖ ≤ a s * B ^ 2)
    (hdet : (a s) ^ 2 * B ^ 4 / 256 ≤
      actualRealCramerDet (b s) (w s))
    (hF : HasDerivAt
      (fun t => -actualHartreeLaplacianScaledKummerSource
        (a t) (ell t) (c t) (z t) r) Fdot s)
    (hS : HasDerivAt
      (fun t => actualMomentLockedScaledScaleSource (a t) (c t) r)
      Sdot s)
    (hP : HasDerivAt
      (fun t => actualMomentLockedScaledPhaseSource (a t) (c t) r)
      Pdot s) :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∃ pbDot pwDot : ℝ,
        let pb : ℝ → ℝ := fun t =>
          (actualRealCramerCorrection (b t) (w t) (Z t)).1
        let pw : ℝ → ℝ := fun t =>
          (actualRealCramerCorrection (b t) (w t) (Z t)).2
        let Sb := actualMomentLockedScaledScaleSource (a s) (c s) r
        let Sw := actualMomentLockedScaledPhaseSource (a s) (c s) r
        let D : ℂ :=
          Fdot - ((pbDot : ℂ) * Sb + (pb s : ℂ) * Sdot) -
            ((pwDot : ℂ) * Sw + (pw s : ℂ) * Pdot)
        HasDerivAt pb pbDot s ∧
        HasDerivAt pw pwDot s ∧
        HasDerivAt
          (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t r)
          D s ∧
        r * ‖D‖ ≤ r * ‖Fdot‖ +
          (1024 * Cs / B ^ 2) *
            ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ +
          |pb s| * (r * ‖Sdot‖) + |pw s| * (r * ‖Pdot‖) := by
  obtain ⟨Cs, hCs, pbDot, pwDot, hpb, hpw, hderiv, hNorm⟩ :=
    actual_Hartree_true_moving_selected_source_time_budget
      a ell c z b w Z s r L B
      hL ha hB hBOne hSmall hr
      bdot wdot Zdot Fdot Sdot Pdot
      hb hw hZ hbNorm hwNorm hdet hF hS hP
  let pb : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).1
  let pw : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).2
  let Sb : ℂ := actualMomentLockedScaledScaleSource (a s) (c s) r
  let Sw : ℂ := actualMomentLockedScaledPhaseSource (a s) (c s) r
  let D : ℂ := Fdot -
    ((pbDot : ℂ) * Sb + (pb s : ℂ) * Sdot) -
    ((pwDot : ℂ) * Sw + (pw s : ℂ) * Pdot)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrpos : 0 < r := (div_pos hLpos ha).trans_le hr.1
  have hCancel :
      r * ((1024 * Cs / (B ^ 2 * r)) *
        ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖) =
      (1024 * Cs / B ^ 2) *
        ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ := by
    field_simp [hrpos.ne', hB.ne']
  have hWeighted : r * ‖D‖ ≤
      r * ‖Fdot‖ +
        (1024 * Cs / B ^ 2) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ +
        |pb s| * (r * ‖Sdot‖) + |pw s| * (r * ‖Pdot‖) := by
    calc
      r * ‖D‖ ≤
          r * (‖Fdot‖ +
            (1024 * Cs / (B ^ 2 * r)) *
              ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ +
            |pb s| * ‖Sdot‖ + |pw s| * ‖Pdot‖) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [D, Sb, Sw, pb, pw] using hNorm
        · exact hrpos.le
      _ = _ := by rw [mul_add, mul_add, mul_add, hCancel]; ring
  refine ⟨Cs, hCs, pbDot, pwDot, ?_, ?_, ?_, ?_⟩
  · simpa only [pb] using hpb
  · simpa only [pw] using hpw
  · simpa only [D, Sb, Sw, pb, pw] using hderiv
  · simpa only [D, Sb, Sw, pb, pw] using hWeighted

end HBL.TypeIIDynamicSelection
