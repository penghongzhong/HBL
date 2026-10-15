import HBL.PhaseQuotient
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Existence of the two normalized compact smooth threshold tests.

The manuscript fixes zeta_+, zeta_- in C_c^infinity((0,infinity)) with
  integral zeta_+ (r Lambda W) = 1,
  integral zeta_- (r W)        = 1.
Here these tests are constructed explicitly from one smooth bump supported
strictly inside (0,1).  Multiplying the bump by the corresponding resonance
and normalizing by the positive integral of bump times resonance squared
gives the required pair.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace HBL.Modulation

/-- The explicit bubble is in fact C-infinity, not merely C1. -/
theorem bubble_contDiff_infty : ContDiff ℝ ∞ bubble := by
  have hA : ContDiff ℝ ∞ (fun r : ℝ => 1 + r ^ 2) := by
    fun_prop
  have hPos (r : ℝ) : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hSqrt :
      ContDiff ℝ ∞ (fun r : ℝ => Real.sqrt (1 + r ^ 2)) :=
    hA.sqrt (fun r => ne_of_gt (hPos r))
  have hSqrtNe (r : ℝ) : Real.sqrt (1 + r ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hPos r))
  change ContDiff ℝ ∞ (fun r : ℝ => (Real.sqrt (1 + r ^ 2))⁻¹)
  exact hSqrt.inv hSqrtNe

/-- Both half-line resonance profiles used by the threshold tests are smooth. -/
theorem radialResonancePlus_contDiff_infty :
    ContDiff ℝ ∞ radialResonancePlus := by
  have hd : ContDiff ℝ ∞ (deriv bubble) :=
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2
  unfold radialResonancePlus dilationGenerator
  exact contDiff_id.mul
    ((bubble_contDiff_infty.div_const 2).add (contDiff_id.mul hd))

theorem radialResonanceMinus_contDiff_infty :
    ContDiff ℝ ∞ radialResonanceMinus := by
  unfold radialResonanceMinus
  exact contDiff_id.mul bubble_contDiff_infty

/-- Closed formula for the scaling generator of W. -/
theorem dilationGenerator_bubble_closed (r : ℝ) :
    dilationGenerator bubble r =
      (1 - r ^ 2) /
        (2 * Real.sqrt (1 + r ^ 2) ^ 3) := by
  have hU := radialU_bubble_deriv_closed r
  rw [radialU_deriv bubble bubble_contDiff r] at hU
  have hrel :
      r * deriv bubble r =
        bubbleRadialEnergyDerivative r - bubble r := by
    linarith
  unfold dilationGenerator
  rw [hrel]
  have hspos : 0 < Real.sqrt (1 + r ^ 2) := by positivity
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := ne_of_gt hspos
  have hs2 :
      Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold bubbleRadialEnergyDerivative bubble
  field_simp [hsne]
  nlinarith [hs2]

/-- The positive resonance is nonzero at the center of the chosen bump. -/
theorem radialResonancePlus_half_ne_zero :
    radialResonancePlus (1 / 2 : ℝ) ≠ 0 := by
  unfold radialResonancePlus
  rw [dilationGenerator_bubble_closed]
  have hspos :
      0 < Real.sqrt (1 + (1 / 2 : ℝ) ^ 2) := by positivity
  apply mul_ne_zero
  · norm_num
  · apply div_ne_zero
    · norm_num
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (ne_of_gt hspos))

theorem radialResonanceMinus_half_ne_zero :
    radialResonanceMinus (1 / 2 : ℝ) ≠ 0 := by
  unfold radialResonanceMinus bubble
  have hspos :
      0 < Real.sqrt (1 + (1 / 2 : ℝ) ^ 2) := by positivity
  exact mul_ne_zero (by norm_num) (inv_ne_zero (ne_of_gt hspos))

/-- A fixed C-infinity bump centered at 1/2 and supported in (1/4,3/4). -/
def thresholdBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem thresholdBump_zero_of_one_le (r : ℝ) (hr : 1 ≤ r) :
    thresholdBump r = 0 := by
  apply thresholdBump.zero_of_le_dist
  change (1 / 4 : ℝ) ≤ dist r (1 / 2 : ℝ)
  rw [Real.dist_eq]
  have h : 0 ≤ r - (1 / 2 : ℝ) := by linarith
  rw [abs_of_nonneg h]
  linarith

theorem thresholdBump_zero_of_nonpos (r : ℝ) (hr : r ≤ 0) :
    thresholdBump r = 0 := by
  apply thresholdBump.zero_of_le_dist
  change (1 / 4 : ℝ) ≤ dist r (1 / 2 : ℝ)
  rw [Real.dist_eq]
  have h : r - (1 / 2 : ℝ) ≤ 0 := by linarith
  rw [abs_of_nonpos h]
  linarith

/-- Positive normalization masses. -/
def thresholdPlusMass : ℝ :=
  ∫ r in (0 : ℝ)..Real.exp 1,
    thresholdBump r * radialResonancePlus r ^ 2

def thresholdMinusMass : ℝ :=
  ∫ r in (0 : ℝ)..Real.exp 1,
    thresholdBump r * radialResonanceMinus r ^ 2

theorem thresholdPlusMass_pos : 0 < thresholdPlusMass := by
  let F : ℝ → ℝ :=
    fun r => thresholdBump r * radialResonancePlus r ^ 2
  have hFcont : Continuous F :=
    thresholdBump.continuous.mul
      (radialResonancePlus_contDiff_infty.continuous.pow 2)
  have hnonneg :
      ∀ r ∈ Ioc (0 : ℝ) (Real.exp 1), 0 ≤ F r := by
    intro r _
    exact mul_nonneg thresholdBump.nonneg (sq_nonneg _)
  have hbhalf : thresholdBump (1 / 2 : ℝ) = 1 := by
    apply thresholdBump.one_of_mem_closedBall
    exact Metric.mem_closedBall_self (by norm_num [thresholdBump])
  have hhalf :
      0 < F (1 / 2 : ℝ) := by
    dsimp [F]
    rw [hbhalf, one_mul]
    exact sq_pos_of_ne_zero radialResonancePlus_half_ne_zero
  have hexp : (1 / 2 : ℝ) ≤ Real.exp 1 := by
    have h1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  unfold thresholdPlusMass
  exact intervalIntegral.integral_pos
    (Real.exp_pos 1)
    hFcont.continuousOn hnonneg
    ⟨1 / 2, ⟨by norm_num, hexp⟩, hhalf⟩

theorem thresholdMinusMass_pos : 0 < thresholdMinusMass := by
  let F : ℝ → ℝ :=
    fun r => thresholdBump r * radialResonanceMinus r ^ 2
  have hFcont : Continuous F :=
    thresholdBump.continuous.mul
      (radialResonanceMinus_contDiff_infty.continuous.pow 2)
  have hnonneg :
      ∀ r ∈ Ioc (0 : ℝ) (Real.exp 1), 0 ≤ F r := by
    intro r _
    exact mul_nonneg thresholdBump.nonneg (sq_nonneg _)
  have hbhalf : thresholdBump (1 / 2 : ℝ) = 1 := by
    apply thresholdBump.one_of_mem_closedBall
    exact Metric.mem_closedBall_self (by norm_num [thresholdBump])
  have hhalf :
      0 < F (1 / 2 : ℝ) := by
    dsimp [F]
    rw [hbhalf, one_mul]
    exact sq_pos_of_ne_zero radialResonanceMinus_half_ne_zero
  have hexp : (1 / 2 : ℝ) ≤ Real.exp 1 := by
    have h1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  unfold thresholdMinusMass
  exact intervalIntegral.integral_pos
    (Real.exp_pos 1)
    hFcont.continuousOn hnonneg
    ⟨1 / 2, ⟨by norm_num, hexp⟩, hhalf⟩

/-- Explicit normalized threshold tests. -/
def normalizedZetaPlus (r : ℝ) : ℝ :=
  thresholdPlusMass⁻¹ * (thresholdBump r * radialResonancePlus r)

def normalizedZetaMinus (r : ℝ) : ℝ :=
  thresholdMinusMass⁻¹ * (thresholdBump r * radialResonanceMinus r)

theorem normalizedZetaPlus_contDiff_infty :
    ContDiff ℝ ∞ normalizedZetaPlus := by
  unfold normalizedZetaPlus
  exact contDiff_const.mul
    (thresholdBump.contDiff.mul radialResonancePlus_contDiff_infty)

theorem normalizedZetaMinus_contDiff_infty :
    ContDiff ℝ ∞ normalizedZetaMinus := by
  unfold normalizedZetaMinus
  exact contDiff_const.mul
    (thresholdBump.contDiff.mul radialResonanceMinus_contDiff_infty)

theorem normalizedZetaPlus_hasCompactSupport :
    HasCompactSupport normalizedZetaPlus := by
  have hb : HasCompactSupport (thresholdBump : ℝ → ℝ) :=
    thresholdBump.hasCompactSupport
  have hbase :
      HasCompactSupport
        (fun r : ℝ => thresholdBump r * radialResonancePlus r) := by
    change HasCompactSupport
      ((thresholdBump : ℝ → ℝ) * radialResonancePlus)
    exact hb.mul_right
  change HasCompactSupport
    ((fun _ : ℝ => thresholdPlusMass⁻¹) *
      (fun r : ℝ => thresholdBump r * radialResonancePlus r))
  exact hbase.mul_left

theorem normalizedZetaMinus_hasCompactSupport :
    HasCompactSupport normalizedZetaMinus := by
  have hb : HasCompactSupport (thresholdBump : ℝ → ℝ) :=
    thresholdBump.hasCompactSupport
  have hbase :
      HasCompactSupport
        (fun r : ℝ => thresholdBump r * radialResonanceMinus r) := by
    change HasCompactSupport
      ((thresholdBump : ℝ → ℝ) * radialResonanceMinus)
    exact hb.mul_right
  change HasCompactSupport
    ((fun _ : ℝ => thresholdMinusMass⁻¹) *
      (fun r : ℝ => thresholdBump r * radialResonanceMinus r))
  exact hbase.mul_left

theorem normalizedZetaPlus_zero_of_one_le (r : ℝ) (hr : 1 ≤ r) :
    normalizedZetaPlus r = 0 := by
  simp [normalizedZetaPlus, thresholdBump_zero_of_one_le r hr]

theorem normalizedZetaMinus_zero_of_one_le (r : ℝ) (hr : 1 ≤ r) :
    normalizedZetaMinus r = 0 := by
  simp [normalizedZetaMinus, thresholdBump_zero_of_one_le r hr]

theorem normalizedZetaPlus_zero_of_nonpos (r : ℝ) (hr : r ≤ 0) :
    normalizedZetaPlus r = 0 := by
  simp [normalizedZetaPlus, thresholdBump_zero_of_nonpos r hr]

theorem normalizedZetaMinus_zero_of_nonpos (r : ℝ) (hr : r ≤ 0) :
    normalizedZetaMinus r = 0 := by
  simp [normalizedZetaMinus, thresholdBump_zero_of_nonpos r hr]

theorem normalizedZetaPlus_normalized :
    (∫ r in (0 : ℝ)..Real.exp 1,
      normalizedZetaPlus r * radialResonancePlus r) = 1 := by
  calc
    (∫ r in (0 : ℝ)..Real.exp 1,
      normalizedZetaPlus r * radialResonancePlus r) =
      ∫ r in (0 : ℝ)..Real.exp 1,
        thresholdPlusMass⁻¹ *
          (thresholdBump r * radialResonancePlus r ^ 2) := by
            apply intervalIntegral.integral_congr
            intro r _
            unfold normalizedZetaPlus
            ring
    _ = thresholdPlusMass⁻¹ * thresholdPlusMass := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = 1 := inv_mul_cancel₀ (ne_of_gt thresholdPlusMass_pos)

theorem normalizedZetaMinus_normalized :
    (∫ r in (0 : ℝ)..Real.exp 1,
      normalizedZetaMinus r * radialResonanceMinus r) = 1 := by
  calc
    (∫ r in (0 : ℝ)..Real.exp 1,
      normalizedZetaMinus r * radialResonanceMinus r) =
      ∫ r in (0 : ℝ)..Real.exp 1,
        thresholdMinusMass⁻¹ *
          (thresholdBump r * radialResonanceMinus r ^ 2) := by
            apply intervalIntegral.integral_congr
            intro r _
            unfold normalizedZetaMinus
            ring
    _ = thresholdMinusMass⁻¹ * thresholdMinusMass := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = 1 := inv_mul_cancel₀ (ne_of_gt thresholdMinusMass_pos)

/-- A concrete pair satisfying the manuscript's test-function choice. -/
theorem normalizedThresholdTests_exist :
    ∃ zPlus zMinus : ℝ → ℝ,
      ContDiff ℝ ∞ zPlus ∧
      ContDiff ℝ ∞ zMinus ∧
      HasCompactSupport zPlus ∧
      HasCompactSupport zMinus ∧
      (∀ r, 1 ≤ r → zPlus r = 0) ∧
      (∀ r, 1 ≤ r → zMinus r = 0) ∧
      (∀ r, r ≤ 0 → zPlus r = 0) ∧
      (∀ r, r ≤ 0 → zMinus r = 0) ∧
      (∫ r in (0 : ℝ)..Real.exp 1,
        zPlus r * radialResonancePlus r) = 1 ∧
      (∫ r in (0 : ℝ)..Real.exp 1,
        zMinus r * radialResonanceMinus r) = 1 := by
  exact ⟨normalizedZetaPlus, normalizedZetaMinus,
    normalizedZetaPlus_contDiff_infty,
    normalizedZetaMinus_contDiff_infty,
    normalizedZetaPlus_hasCompactSupport,
    normalizedZetaMinus_hasCompactSupport,
    normalizedZetaPlus_zero_of_one_le,
    normalizedZetaMinus_zero_of_one_le,
    normalizedZetaPlus_zero_of_nonpos,
    normalizedZetaMinus_zero_of_nonpos,
    normalizedZetaPlus_normalized,
    normalizedZetaMinus_normalized⟩

end HBL.Modulation
