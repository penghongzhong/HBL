import HBL.InnerEstimates.OutputLinearity
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedResponseMomentGrowth
import Mathlib.Tactic

/-!
# The physical source-norm cost of the actual coupled speed correction

Unlike the structural packet order, these estimates use the genuine
L^{2,7/4} source norm.  The two adjusted sources are the SAME functions used
by the matched Kummer backward-shell construction. The speed-source growth
is obtained from the fixed Fredholm source analysis, not assumed.

A precise obstruction input Z is retained in the final inequality. This
module does not derive a uniform bound for Z from the original Hartree
residual, nor does it claim a global PDE residual gain or manuscript 2.13.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology RealInnerProductSpace

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole
open HBL.Modulation.AffineTail
open HBL.Profile.ActualInner

/-- Actual weighted L2 triangle inequality for the source and its
modulation direction, using the same source-data L2 representatives. -/
theorem actual_weighted_source_norm_add_smul_le
    (sigma : ℝ) (F G : ℝ → ℝ)
    (hF : InWeightedL2 sigma F) (hG : InWeightedL2 sigma G)
    (d : ℝ) (hH : InWeightedL2 sigma (fun r => F r + d * G r)) :
    innerWeightedNorm sigma (fun r => F r + d * G r) ≤
      innerWeightedNorm sigma F + |d| * innerWeightedNorm sigma G := by
  have h := norm_add_le
    (weightedSourceDataL2 sigma F hF)
    (d • weightedSourceDataL2 sigma G hG)
  rw [← weightedSourceDataL2_add_smul sigma F G hF hG d hH] at h
  simpa only [norm_smul, Real.norm_eq_abs, ← innerWeightedNorm_eq] using h

/-- Exact norm bridge for the actual scale and phase sources. It imposes
no smallness on the speed increment or the original source. -/
theorem actual_Hartree_moment_locked_adjusted_source_norm_bound
    (L c : ℝ) (hL : 0 < L) (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (db dw : ℝ) :
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    innerWeightedNorm (7 / 4 : ℝ) (fun r => Fp r + dw * Gp r) +
      innerWeightedNorm (7 / 4 : ℝ) (fun r => Fm r + db * Gm r) ≤
        innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm +
          |dw| * innerWeightedNorm (7 / 4 : ℝ) Gp +
          |db| * innerWeightedNorm (7 / 4 : ℝ) Gm := by
  dsimp only
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  have hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
  have hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
  have hp' := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp dw
  have hm' := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm db
  have hpBound := actual_weighted_source_norm_add_smul_le
    (7 / 4 : ℝ) Fp Gp hp hgp dw hp'
  have hmBound := actual_weighted_source_norm_add_smul_le
    (7 / 4 : ℝ) Fm Gm hm hgm db hm'
  calc
    _ ≤ (innerWeightedNorm (7 / 4 : ℝ) Fp +
        |dw| * innerWeightedNorm (7 / 4 : ℝ) Gp) +
        (innerWeightedNorm (7 / 4 : ℝ) Fm +
        |db| * innerWeightedNorm (7 / 4 : ℝ) Gm) :=
          add_le_add hpBound hmBound
    _ = _ := by ring

/-- The *actual* physical speed sources have the uniform quartic cost
already proved in the moment-growth source analysis. -/
theorem actual_Hartree_moment_locked_adjusted_source_quartic_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (L c : ℝ) (_hL : 1 ≤ L), |c| ≤ 1 →
      ∀ (Fp Fm : ℝ → ℝ)
        (_hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (_hm : InWeightedL2 (7 / 4 : ℝ) Fm) (db dw : ℝ),
        let Gp := actualMomentLockedInnerPhaseSource L c
        let Gm := actualMomentLockedInnerScaleSource L c
        innerWeightedNorm (7 / 4 : ℝ) (fun r => Fp r + dw * Gp r) +
          innerWeightedNorm (7 / 4 : ℝ) (fun r => Fm r + db * Gm r) ≤
            innerWeightedNorm (7 / 4 : ℝ) Fp +
              innerWeightedNorm (7 / 4 : ℝ) Fm +
              C * L ^ 4 * (|db| + |dw|) := by
  obtain ⟨C, hC, hGrowth⟩ :=
    actual_Hartree_moment_locked_response_moment_growth
  refine ⟨C, hC, ?_⟩
  intro L c hL hc Fp Fm hp hm db dw
  dsimp only
  let hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  have hRaw := actual_Hartree_moment_locked_adjusted_source_norm_bound
    L c hLp Fp Fm hp hm db dw
  have hData := hGrowth L c hL hc
  dsimp only at hData
  have hPg : innerWeightedNorm (7 / 4 : ℝ) Gp ≤ C * L ^ 4 :=
    hData.1.2
  have hMg : innerWeightedNorm (7 / 4 : ℝ) Gm ≤ C * L ^ 4 :=
    hData.1.1
  have hP := mul_le_mul_of_nonneg_left hPg (abs_nonneg dw)
  have hM := mul_le_mul_of_nonneg_left hMg (abs_nonneg db)
  calc
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm +
        |dw| * innerWeightedNorm (7 / 4 : ℝ) Gp +
        |db| * innerWeightedNorm (7 / 4 : ℝ) Gm := hRaw
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm +
        |dw| * (C * L ^ 4) + |db| * (C * L ^ 4) := by
          linarith only [hP, hM]
    _ = _ := by ring

/-- The exact speed-inverse-to-source bridge. The real speed-inverse
inequality is a separate producer already proved for the complete
compatibility matrix. This theorem does not silently replace the actual
obstruction by an unproved original residual norm. -/
theorem actual_Hartree_moment_locked_adjusted_source_obstruction_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (L c a B : ℝ) (_hL : 1 ≤ L), |c| ≤ 1 →
      ∀ (Fp Fm : ℝ → ℝ)
        (_hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (_hm : InWeightedL2 (7 / 4 : ℝ) Fm)
        (db dw : ℝ) (Z : ℂ),
        |db| + |dw| ≤ 1024 / (a * B ^ 2) * ‖Z‖ →
        let Gp := actualMomentLockedInnerPhaseSource L c
        let Gm := actualMomentLockedInnerScaleSource L c
        innerWeightedNorm (7 / 4 : ℝ) (fun r => Fp r + dw * Gp r) +
          innerWeightedNorm (7 / 4 : ℝ) (fun r => Fm r + db * Gm r) ≤
            innerWeightedNorm (7 / 4 : ℝ) Fp +
              innerWeightedNorm (7 / 4 : ℝ) Fm +
              (1024 * C * L ^ 4 / (a * B ^ 2)) * ‖Z‖ := by
  obtain ⟨C, hC, hBound⟩ :=
    actual_Hartree_moment_locked_adjusted_source_quartic_bound
  refine ⟨C, hC, ?_⟩
  intro L c a B hL hc Fp Fm hp hm db dw Z hSpeed
  dsimp only
  have hSource := hBound L c hL hc Fp Fm hp hm db dw
  dsimp only at hSource
  have hCoeff : 0 ≤ C * L ^ 4 :=
    mul_nonneg hC (pow_nonneg (by linarith : (0 : ℝ) ≤ L) 4)
  calc
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm +
          C * L ^ 4 * (|db| + |dw|) := hSource
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm +
          C * L ^ 4 * (1024 / (a * B ^ 2) * ‖Z‖) :=
            by linarith only [mul_le_mul_of_nonneg_left hSpeed hCoeff]
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
