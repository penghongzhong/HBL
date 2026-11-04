import HBL.TypeIIDynamicSelection.ActualHartreeNonlocalWeightedQuantitative
import HBL.InnerEstimates.Definitions
import Mathlib.Tactic

/-!
# The original conjugated source norm of a physical shell error

The original Fredholm source is r times the physical PDE error.  On a
shell [R,2R], the L^{2,7/4}(dr) cost of a bounded physical error is
R^{13/4}; both the radial factor and the square-root shell volume are
retained.  This converts an R^{-4} physical equation error into an
R^{-3/4} relative source-norm gain.

The function below is the magnitude of the actual conjugated shell
piece, supported on the open shell. Endpoints have zero measure.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualConjugatedShellMagnitude (R : ℝ) (E : ℝ → ℂ) : ℝ → ℝ :=
  (Ioo R (2 * R)).indicator (fun r => r * ‖E r‖)

/-- The actual weighted norm includes the conjugation and shell-volume
factors. The estimate also proves membership in the original source space. -/
theorem actual_conjugated_shell_weighted_norm
    (R A : ℝ) (hR : 0 < R) (hA : 0 ≤ A)
    (E : ℝ → ℂ) (hE : Measurable E)
    (hbound : ∀ r ∈ Icc R (2 * R), ‖E r‖ ≤ A) :
    InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
      innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ≤
        (affineJapaneseWeight (7 / 4 : ℝ) (2 * R) * (2 * R * A)) *
          Real.sqrt (2 * R) := by
  let S := actualConjugatedShellMagnitude R E
  let W : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r * S r
  let B := affineJapaneseWeight (7 / 4 : ℝ) (2 * R) * (2 * R * A)
  have hweight (r : ℝ) : 0 ≤ affineJapaneseWeight (7 / 4 : ℝ) r := by
    unfold affineJapaneseWeight
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hSmeas : Measurable S := (measurable_id.mul hE.norm).indicator measurableSet_Ioo
  have hWmeas : Measurable W :=
    (affineJapaneseWeight_continuous (7 / 4 : ℝ)).measurable.mul hSmeas
  have hSnonneg (r : ℝ) : 0 ≤ S r := by
    by_cases hr : r ∈ Ioo R (2 * R)
    · change 0 ≤ (Ioo R (2 * R)).indicator (fun t => t * ‖E t‖) r
      rw [indicator_of_mem hr]
      exact mul_nonneg (hR.trans hr.1).le (norm_nonneg _)
    · change 0 ≤ (Ioo R (2 * R)).indicator (fun t => t * ‖E t‖) r
      rw [indicator_of_notMem hr]
  have hWnonneg (r : ℝ) : 0 ≤ W r := mul_nonneg (hweight r) (hSnonneg r)
  have hWbound (r : ℝ) (hr : 0 < r) (hcap : r ≤ 2 * R) : W r ≤ B := by
    by_cases hs : r ∈ Ioo R (2 * R)
    · have hw : affineJapaneseWeight (7 / 4 : ℝ) r ≤
          affineJapaneseWeight (7 / 4 : ℝ) (2 * R) := by
        unfold affineJapaneseWeight
        apply Real.rpow_le_rpow (by positivity)
          (by nlinarith [pow_le_pow_left₀ hr.le hcap 2])
        norm_num
      have hv : r * ‖E r‖ ≤ 2 * R * A :=
        mul_le_mul hcap (hbound r ⟨hs.1.le, hs.2.le⟩) (norm_nonneg _) (by positivity)
      change affineJapaneseWeight (7 / 4 : ℝ) r *
        (Ioo R (2 * R)).indicator (fun t => t * ‖E t‖) r ≤ B
      rw [indicator_of_mem hs]
      exact mul_le_mul hw hv (mul_nonneg hr.le (norm_nonneg _)) (hweight _)
    · change affineJapaneseWeight (7 / 4 : ℝ) r *
        (Ioo R (2 * R)).indicator (fun t => t * ‖E t‖) r ≤ B
      rw [indicator_of_notMem hs, mul_zero]
      exact hB
  have hWzero (r : ℝ) (hr : 2 * R ≤ r) : W r = 0 := by
    have hs : r ∉ Ioo R (2 * R) := fun h => (not_lt_of_ge hr) h.2
    simp [W, S, actualConjugatedShellMagnitude, hs]
  let G : ℝ → ℝ := (Ioc (0 : ℝ) (2 * R)).indicator (fun _ => B)
  have hG : MemLp G 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet B
      (.inr measure_Ioc_lt_top.ne)
  have hdom (r : ℝ) : ‖W r‖ ≤ ‖G r‖ := by
    by_cases hr : r ∈ Ioc (0 : ℝ) (2 * R)
    · change ‖W r‖ ≤ ‖(Ioc (0 : ℝ) (2 * R)).indicator (fun _ => B) r‖
      rw [indicator_of_mem hr, Real.norm_eq_abs, abs_of_nonneg (hWnonneg r),
        Real.norm_eq_abs, abs_of_nonneg hB]
      exact hWbound r hr.1 hr.2
    · have hs : r ∉ Ioo R (2 * R) := by
        intro hs
        exact hr ⟨hR.trans hs.1, hs.2.le⟩
      simp [W, S, G, actualConjugatedShellMagnitude, hs, hr]
  have hmem : MemLp W 2 (volume : Measure ℝ) :=
    hG.mono' hWmeas.aestronglyMeasurable (Filter.Eventually.of_forall hdom)
  refine ⟨hmem.mono_measure Measure.restrict_le_self, ?_⟩
  exact actual_supported_halfLine_L2_norm_le R B hR hB W hWmeas
    hWnonneg hWbound hWzero

private theorem actual_shell_geometric_norm_factor
    (R : ℝ) (hR : 1 ≤ R) :
    affineJapaneseWeight (7 / 4 : ℝ) (2 * R) * (2 * R) * Real.sqrt (2 * R) ≤
      20 * R ^ (13 / 4 : ℝ) := by
  have hRpos : 0 < R := by linarith
  have hweight : affineJapaneseWeight (7 / 4 : ℝ) (2 * R) ≤
      5 * R ^ (7 / 4 : ℝ) := by
    have hbase : 1 + (2 * R) ^ 2 ≤ 5 * R ^ 2 := by nlinarith
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + (2 * R) ^ 2)
      hbase (show (0 : ℝ) ≤ 7 / 8 by norm_num)
    have hfive : (5 : ℝ) ^ (7 / 8 : ℝ) ≤ 5 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 5 by norm_num) (show (7 / 8 : ℝ) ≤ 1 by norm_num)
    have hpower : (R ^ 2) ^ (7 / 8 : ℝ) = R ^ (7 / 4 : ℝ) := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hRpos.le]
      norm_num
    change (1 + (2 * R) ^ 2) ^ ((7 / 4 : ℝ) / 2) ≤ _
    norm_num only [show (7 / 4 : ℝ) / 2 = 7 / 8 by norm_num]
    calc
      _ ≤ (5 * R ^ 2) ^ (7 / 8 : ℝ) := hp
      _ = (5 : ℝ) ^ (7 / 8 : ℝ) * R ^ (7 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (sq_nonneg R), hpower]
      _ ≤ 5 * R ^ (7 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hfive (Real.rpow_nonneg hRpos.le _)
  have hsqrt : Real.sqrt (2 * R) ≤ 2 * R ^ (1 / 2 : ℝ) := by
    have hs : Real.sqrt (2 : ℝ) ≤ 2 := by norm_num
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hRpos.le _)
  calc
    _ ≤ (5 * R ^ (7 / 4 : ℝ)) * (2 * R) * (2 * R ^ (1 / 2 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hweight (by positivity)) hsqrt
        (Real.sqrt_nonneg _) (by positivity)
    _ = 20 * R ^ (13 / 4 : ℝ) := by
      have hp : R ^ (7 / 4 : ℝ) * R * R ^ (1 / 2 : ℝ) =
          R ^ (13 / 4 : ℝ) := by
        calc
          _ = R ^ (7 / 4 : ℝ) * R ^ (1 : ℝ) * R ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
          _ = R ^ ((7 / 4 : ℝ) + 1 + 1 / 2) := by
            rw [← Real.rpow_add hRpos, ← Real.rpow_add hRpos]
          _ = _ := by norm_num
      nlinarith [hp]

/-- Exact original source-space power. No spatial volume or conjugation
loss is omitted when the shell error is returned to the fixed inverse. -/
theorem actual_conjugated_shell_weighted_power_bound
    (R A : ℝ) (hR : 1 ≤ R) (hA : 0 ≤ A)
    (E : ℝ → ℂ) (hE : Measurable E)
    (hbound : ∀ r ∈ Icc R (2 * R), ‖E r‖ ≤ A) :
    InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
      innerWeightedNorm (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ≤
        20 * R ^ (13 / 4 : ℝ) * A := by
  have hRpos : 0 < R := by linarith
  have h := actual_conjugated_shell_weighted_norm R A hRpos hA E hE hbound
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ = (affineJapaneseWeight (7 / 4 : ℝ) (2 * R) * (2 * R) *
        Real.sqrt (2 * R)) * A := by ring
    _ ≤ (20 * R ^ (13 / 4 : ℝ)) * A :=
      mul_le_mul_of_nonneg_right (actual_shell_geometric_norm_factor R hR) hA

end HBL.TypeIIDynamicSelection
