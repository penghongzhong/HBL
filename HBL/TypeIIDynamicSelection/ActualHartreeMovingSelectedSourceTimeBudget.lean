import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreen
import Mathlib.Tactic

/-!
# Genuine moving Hartree selected source: quantitative time-derivative budget

The original 3D inverse-square quartic Riesz source F0(s,r), and BOTH actual
scaled scale/phase source directions Sb(s,r), Sw(s,r), are time dependent.
The two real speeds are computed by the genuine Cramer selector.

The previously strict Cramer derivative theorem gives the actual speed
derivatives (not hypotheses), and the previously strict moving-annulus
envelopes prove ||Sb||,||Sw|| <= Cs*a/r. Their combination cancels the
potential 1/a loss in the time derivative from the determinant inverse:
the speed-derivative contribution costs only 1024*Cs/(B^2*r) times the
derivative of the original compatibility obstruction/columns.

The derivative values of the ORIGINAL full Hartree source and both evolving
physical source profiles remain explicitly required. No fixed Type-II rate,
synthetic forcing, arbitrary independent modulation derivative or residual
smallness is assumed. This is a pointwise analytic budget, not yet the
weighted O(s^(-9/4)) full four-piece PDE residual.
-/

noncomputable section
set_option autoImplicit false

open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_moving_selected_source_time_budget
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
        ‖D‖ ≤ ‖Fdot‖ +
          (1024 * Cs / (B ^ 2 * r)) *
            ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ +
          |pb s| * ‖Sdot‖ + |pw s| * ‖Pdot‖ := by
  obtain ⟨Cs, hCs, hEnvelope⟩ :=
    actual_Hartree_scaled_speed_outer_inverse_radius
  obtain ⟨pbDot, pwDot, hpb, hpw, hspeed, hderiv⟩ :=
    actual_Hartree_true_moving_adjusted_source_derivative
      a ell c z b w Z s r (a s) B ha hB
      bdot wdot Zdot Fdot Sdot Pdot
      hb hw hZ hbNorm hwNorm hdet hF hS hP
  let pb : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).1
  let pw : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).2
  let Sb : ℂ := actualMomentLockedScaledScaleSource (a s) (c s) r
  let Sw : ℂ := actualMomentLockedScaledPhaseSource (a s) (c s) r
  let Db : ℂ := (pbDot : ℂ) * Sb + (pb s : ℂ) * Sdot
  let Dw : ℂ := (pwDot : ℂ) * Sw + (pw s : ℂ) * Pdot
  let C0 : ℝ := Cs * a s / r
  let D : ℂ := Fdot - Db - Dw
  have hSbound : ‖Sb‖ ≤ C0 := by
    simpa only [Sb, C0] using
      (hEnvelope L (c s) (a s) B hL ha hBOne hSmall r hr).1
  have hPbound : ‖Sw‖ ≤ C0 := by
    simpa only [Sw, C0] using
      (hEnvelope L (c s) (a s) B hL ha hBOne hSmall r hr).2
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrpos : 0 < r := (div_pos hLpos ha).trans_le hr.1
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hDb :
      ‖Db‖ ≤ |pbDot| * C0 + |pb s| * ‖Sdot‖ := by
    calc
      ‖Db‖ ≤ ‖(pbDot : ℂ) * Sb‖ + ‖(pb s : ℂ) * Sdot‖ := norm_add_le _ _
      _ = |pbDot| * ‖Sb‖ + |pb s| * ‖Sdot‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |pbDot| * C0 + |pb s| * ‖Sdot‖ := by
        have hbNorm := mul_le_mul_of_nonneg_left hSbound (abs_nonneg pbDot)
        linarith only [hbNorm]
  have hDw :
      ‖Dw‖ ≤ |pwDot| * C0 + |pw s| * ‖Pdot‖ := by
    calc
      ‖Dw‖ ≤ ‖(pwDot : ℂ) * Sw‖ + ‖(pw s : ℂ) * Pdot‖ := norm_add_le _ _
      _ = |pwDot| * ‖Sw‖ + |pw s| * ‖Pdot‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |pwDot| * C0 + |pw s| * ‖Pdot‖ := by
        have hwNorm := mul_le_mul_of_nonneg_left hPbound (abs_nonneg pwDot)
        linarith only [hwNorm]
  have hDetBudget :
      (|pbDot| + |pwDot|) * C0 ≤
        (1024 * Cs / (B ^ 2 * r)) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ := by
    calc
      _ ≤ (1024 / (a s * B ^ 2) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖) * C0 :=
        mul_le_mul_of_nonneg_right
          (by simpa only [pb, pw] using hspeed) hC0
      _ = _ := by
        dsimp [C0]
        field_simp [ha.ne', hB.ne', hrpos.ne']
  have hRaw :
      ‖D‖ ≤ ‖Fdot‖ + ((|pbDot| + |pwDot|) * C0 +
        |pb s| * ‖Sdot‖ + |pw s| * ‖Pdot‖) := by
    calc
      ‖D‖ ≤ (‖Fdot‖ + ‖Db‖) + ‖Dw‖ := by
        calc
          _ ≤ ‖Fdot - Db‖ + ‖Dw‖ := norm_sub_le _ _
          _ ≤ (‖Fdot‖ + ‖Db‖) + ‖Dw‖ := by
            have hsub := norm_sub_le Fdot Db
            linarith only [hsub]
      _ ≤ (‖Fdot‖ + (|pbDot| * C0 + |pb s| * ‖Sdot‖)) +
          (|pwDot| * C0 + |pw s| * ‖Pdot‖) := by
        linarith only [hDb, hDw]
      _ = _ := by ring
  have hMain :
      ‖D‖ ≤ ‖Fdot‖ +
        (1024 * Cs / (B ^ 2 * r)) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ +
        |pb s| * ‖Sdot‖ + |pw s| * ‖Pdot‖ := by
    calc
      _ ≤ ‖Fdot‖ +
        ((|pbDot| + |pwDot|) * C0 +
          |pb s| * ‖Sdot‖ + |pw s| * ‖Pdot‖) := hRaw
      _ ≤ ‖Fdot‖ +
        ((1024 * Cs / (B ^ 2 * r)) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ +
          |pb s| * ‖Sdot‖ + |pw s| * ‖Pdot‖) := by
        linarith only [hDetBudget]
      _ = _ := by ring
  refine ⟨Cs, hCs, pbDot, pwDot, ?_, ?_, ?_, ?_⟩
  · simpa only [pb] using hpb
  · simpa only [pw] using hpw
  · simpa only [D, Db, Dw, Sb, Sw, pb, pw] using hderiv
  · simpa only [D, Db, Dw, Sb, Sw, pb, pw] using hMain

end HBL.TypeIIDynamicSelection
