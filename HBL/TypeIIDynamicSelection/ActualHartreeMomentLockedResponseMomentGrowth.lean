import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedResponseTraceBound
import HBL.TypeIIDynamicSelection.ActualHartreeNonlocalWeightedQuantitative
import HBL.InnerEstimates.WeightedNormIdentity
import HBL.InnerEstimates.WeightedNormNonnegative
import HBL.InnerEstimates.ZeroData

/-!
A coarse polynomial bound for the genuine moment-locked response data.
For L >= 1 and |c| <= 1 the two physical inputs, their forced affine
charges, their corrected weighted norms, and their reconstructed Green
moments are all bounded by one fixed constant times L^4. The constant
is derived from the physical profile bounds and the fixed Fredholm
operators; no moving response or inverse estimate is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

private theorem actual_moment_bubble_dilation_abs_le_one (r : ℝ) :
    |dilationGenerator bubble r| ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (1 + r ^ 2) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + r ^ 2 by nlinarith [sq_nonneg r])
    simpa only [Real.sqrt_one] using h
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hdiff : |1 - r ^ 2| ≤ 1 + r ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg r]
  rw [dilationGenerator_bubble_closed, abs_div,
    abs_of_pos (by positivity : 0 < 2 * Real.sqrt (1 + r ^ 2) ^ 3)]
  rw [div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (1 + r ^ 2) ^ 3)]
  nlinarith [sq_nonneg (Real.sqrt (1 + r ^ 2)),
    mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (Real.sqrt (1 + r ^ 2)))]

private theorem actual_moment_inner_sources_measurable (L c : ℝ) :
    Measurable (actualMomentLockedInnerScaleSource L c) ∧
    Measurable (actualMomentLockedInnerPhaseSource L c) := by
  have hCore : Measurable (actualMomentLockedCore c) :=
    monopoleMovingCutoffProfile_measurable.comp (measurable_const.prodMk measurable_id)
  have hP : Measurable monopoleRadialProfile :=
    monopoleProfile_continuous.measurable.div measurable_id
  have hChi : Measurable cutoff := cutoff_contDiff_infty.continuous.measurable
  have hDChi : Measurable (deriv cutoff) := measurable_deriv cutoff
  have hT : Measurable (actualMomentLockedAmplitudeTangent c) := by
    unfold actualMomentLockedAmplitudeTangent
    fun_prop
  have hDCore : Measurable (deriv (actualMomentLockedCore c)) := measurable_deriv _
  have hQ : Measurable (actualMomentLockedScaleProfile c) := by
    unfold actualMomentLockedScaleProfile dilationGenerator
    fun_prop
  have hCut : Measurable (actualHartreeInnerSourceCutoff L) :=
    (actual_Hartree_inner_source_cutoff_continuous L).measurable
  exact ⟨(measurable_id.mul hCut).mul hQ,
    (measurable_id.mul hCut).mul hCore⟩

private theorem actual_compact_inner_weighted_norm_quartic
    (L A : ℝ) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (F : ℝ → ℝ) (hF : Measurable F)
    (hBound : ∀ r, 0 < r → r ≤ 2 * L → |F r| ≤ 2 * L * A)
    (hZero : ∀ r, 2 * L ≤ r → F r = 0) :
    innerWeightedNorm (7 / 4 : ℝ) F ≤ (20 * A) * L ^ 4 := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  let S : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r * F r
  have hS : Measurable S :=
    (affineJapaneseWeight_continuous _).measurable.mul hF
  have hPoint (r : ℝ) (hr : 0 < r) (hrL : r ≤ 2 * L) :
      ‖S r‖ ≤ 10 * A * L ^ 3 := by
    have hw0 : 0 ≤ affineJapaneseWeight (7 / 4 : ℝ) r := by
      unfold affineJapaneseWeight
      positivity
    have hw : affineJapaneseWeight (7 / 4 : ℝ) r ≤ 5 * L ^ 2 := by
      calc
        _ ≤ 1 + r ^ 2 :=
          affineJapaneseWeight_le_one_add_sq (7 / 4 : ℝ) r (by norm_num)
        _ ≤ 5 * L ^ 2 := by
          nlinarith [pow_le_pow_left₀ hr.le hrL 2, sq_nonneg (L - 1)]
    dsimp [S]
    rw [abs_mul, abs_of_nonneg hw0]
    calc
      _ ≤ (5 * L ^ 2) * (2 * L * A) :=
        mul_le_mul hw (hBound r hr hrL) (abs_nonneg _) (by positivity)
      _ = 10 * A * L ^ 3 := by ring
  have hFar (r : ℝ) (hr : 2 * L ≤ r) : ‖S r‖ = 0 := by
    simp only [S, hZero r hr, mul_zero, norm_zero]
  have hNorm := actual_supported_halfLine_L2_norm_le
    L (10 * A * L ^ 3) hLp (by positivity) (fun r => ‖S r‖)
    hS.norm (fun _ => norm_nonneg _) hPoint hFar
  rw [eLpNorm_norm S hS.aestronglyMeasurable] at hNorm
  change innerWeightedNorm (7 / 4 : ℝ) F ≤
    (10 * A * L ^ 3) * Real.sqrt (2 * L) at hNorm
  have hsqrt : Real.sqrt (2 * L) ≤ 2 * L := by
    calc
      _ ≤ Real.sqrt ((2 * L) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (L - 1)])
      _ = 2 * L := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (10 * A * L ^ 3) * Real.sqrt (2 * L) := hNorm
    _ ≤ (10 * A * L ^ 3) * (2 * L) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = (20 * A) * L ^ 4 := by ring

private theorem actual_moment_inner_source_norm_growth :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (L c : ℝ), 1 ≤ L → |c| ≤ 1 →
      innerWeightedNorm (7 / 4 : ℝ) (actualMomentLockedInnerScaleSource L c) ≤
        A * L ^ 4 ∧
      innerWeightedNorm (7 / 4 : ℝ) (actualMomentLockedInnerPhaseSource L c) ≤
        A * L ^ 4 := by
  obtain ⟨M, hM, hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  refine ⟨20 * (M + 1), by positivity, ?_⟩
  intro L c hL hc
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hProfile (r : ℝ) (hr : 0 < r) :
      |actualMomentLockedScaleProfile c r| ≤ M + 1 ∧
      |actualMomentLockedCore c r| ≤ M + 1 := by
    have hMc : M * |c| ≤ M := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hc hM.le
    constructor
    · have hTriangle := abs_add_le
        (actualMomentLockedScaleProfile c r - dilationGenerator bubble r)
        (dilationGenerator bubble r)
      rw [sub_add_cancel] at hTriangle
      exact hTriangle.trans (_root_.add_le_add
        ((hClose c r hr).1.trans hMc) (actual_moment_bubble_dilation_abs_le_one r))
    · have hTriangle := abs_add_le
        (actualMomentLockedCore c r - bubble r) (bubble r)
      rw [sub_add_cancel] at hTriangle
      exact hTriangle.trans (_root_.add_le_add
        ((hClose c r hr).2.trans hMc) (bubble_abs_le_one r))
  have hInputs (r : ℝ) (hr : 0 < r) :
      |actualMomentLockedInnerScaleSource L c r| ≤ 2 * L * (M + 1) ∧
      |actualMomentLockedInnerPhaseSource L c r| ≤ 2 * L * (M + 1) := by
    have hMul := actual_Hartree_inner_radial_multiplier_bound L r hLp hr
    constructor
    · unfold actualMomentLockedInnerScaleSource
      rw [abs_mul]
      exact mul_le_mul hMul (hProfile r hr).1 (abs_nonneg _) (by positivity)
    · unfold actualMomentLockedInnerPhaseSource
      rw [abs_mul]
      exact mul_le_mul hMul (hProfile r hr).2 (abs_nonneg _) (by positivity)
  have hMeas := actual_moment_inner_sources_measurable L c
  exact ⟨actual_compact_inner_weighted_norm_quartic L (M + 1) hL (by positivity)
      _ hMeas.1 (fun r hr _ => (hInputs r hr).1)
      (fun r hr => (actual_Hartree_moment_locked_inner_sources_exterior L c r hLp hr).1),
    actual_compact_inner_weighted_norm_quartic L (M + 1) hL (by positivity)
      _ hMeas.2 (fun r hr _ => (hInputs r hr).2)
      (fun r hr => (actual_Hartree_moment_locked_inner_sources_exterior L c r hLp hr).2.1)⟩

private theorem actual_fixed_charge_correction_norm_constant :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : ℝ → ℝ) (hF : InWeightedL2 (7 / 4 : ℝ) F),
      |actualMinusCharge F| ≤ K * innerWeightedNorm (7 / 4 : ℝ) F ∧
      |actualPlusCharge F| ≤ K * innerWeightedNorm (7 / 4 : ℝ) F ∧
      ‖correctedMinusDataL2 (7 / 4 : ℝ) (by norm_num) F hF‖ ≤
        K * innerWeightedNorm (7 / 4 : ℝ) F ∧
      ‖correctedPlusDataL2 (7 / 4 : ℝ) (by norm_num) F hF‖ ≤
        K * innerWeightedNorm (7 / 4 : ℝ) F := by
  let Cp : ℝ := 2 * ‖weightedSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖
  let Cm : ℝ := ‖weightedPhaseSourceResonanceL2 (7 / 4 : ℝ) (by norm_num)‖
  let Kp : ℝ := 1 + Cp * ‖plusAffineSourceDataL2 (7 / 4 : ℝ) (by norm_num)‖
  let Km : ℝ := 1 + Cm * ‖minusAffineSourceDataL2 (7 / 4 : ℝ) (by norm_num)‖
  let K : ℝ := Cp + Cm + Kp + Km
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hCm : 0 ≤ Cm := norm_nonneg _
  have hKp : 0 ≤ Kp := by dsimp [Kp]; positivity
  have hKm : 0 ≤ Km := by dsimp [Km]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCpK : Cp ≤ K := by dsimp [K]; linarith
  have hCmK : Cm ≤ K := by dsimp [K]; linarith
  have hKpK : Kp ≤ K := by dsimp [K]; linarith
  have hKmK : Km ≤ K := by dsimp [K]; linarith
  have h0 : InWeightedL2 (7 / 4 : ℝ) (fun _ => 0) := by simp [InWeightedL2]
  have hp0 : actualPlusCharge (fun _ => 0) = 0 := by
    simp [actualPlusCharge, channelPairing]
  have hm0 : actualMinusCharge (fun _ => 0) = 0 := by
    simp [actualMinusCharge, channelPairing]
  have hpc0 : correctedPlusDataL2 (7 / 4 : ℝ) (by norm_num) (fun _ => 0) h0 = 0 := by
    rw [correctedPlusDataL2_eq, innerWeightedData_zero, hp0]
    simp
  have hmc0 : correctedMinusDataL2 (7 / 4 : ℝ) (by norm_num) (fun _ => 0) h0 = 0 := by
    rw [correctedMinusDataL2_eq, innerWeightedData_zero, hm0]
    simp
  refine ⟨K, hK, ?_⟩
  intro F hF
  have hNorm := innerWeightedNorm_nonneg (7 / 4 : ℝ) F
  have hChargep : |actualPlusCharge F| ≤ Cp * innerWeightedNorm (7 / 4 : ℝ) F := by
    have h := actualPlusCharge_difference_le (7 / 4 : ℝ) (by norm_num)
      F (fun _ => 0) hF h0
    simpa only [hp0, innerWeightedData_zero, sub_zero, Real.norm_eq_abs,
      Cp, ← innerWeightedNorm_eq] using h
  have hChargem : |actualMinusCharge F| ≤ Cm * innerWeightedNorm (7 / 4 : ℝ) F := by
    have h := actualMinusCharge_difference_le (7 / 4 : ℝ) (by norm_num)
      F (fun _ => 0) hF h0
    simpa only [hm0, innerWeightedData_zero, sub_zero, Real.norm_eq_abs,
      Cm, ← innerWeightedNorm_eq] using h
  have hCorrectp : ‖correctedPlusDataL2 (7 / 4 : ℝ) (by norm_num) F hF‖ ≤
      Kp * innerWeightedNorm (7 / 4 : ℝ) F := by
    have h := correctedPlusDataL2_difference_le (7 / 4 : ℝ) (by norm_num) (by norm_num)
      F (fun _ => 0) hF h0
    simpa only [hpc0, innerWeightedData_zero, sub_zero, Kp, Cp,
      ← innerWeightedNorm_eq] using h
  have hCorrectm : ‖correctedMinusDataL2 (7 / 4 : ℝ) (by norm_num) F hF‖ ≤
      Km * innerWeightedNorm (7 / 4 : ℝ) F := by
    have h := correctedMinusDataL2_difference_le (7 / 4 : ℝ) (by norm_num) (by norm_num)
      F (fun _ => 0) hF h0
    simpa only [hmc0, innerWeightedData_zero, sub_zero, Km, Cm,
      ← innerWeightedNorm_eq] using h
  exact ⟨hChargem.trans (mul_le_mul_of_nonneg_right hCmK hNorm),
    hChargep.trans (mul_le_mul_of_nonneg_right hCpK hNorm),
    hCorrectm.trans (mul_le_mul_of_nonneg_right hKmK hNorm),
    hCorrectp.trans (mul_le_mul_of_nonneg_right hKpK hNorm)⟩

/-- One fixed polynomial growth bound for both true response channels.
The conclusion is grouped as original norms, forced charges, corrected
norms, and full Green moments, in that order. -/
theorem actual_Hartree_moment_locked_response_moment_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L c : ℝ) (hL : 1 ≤ L), |c| ≤ 1 →
      let hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL
      (innerWeightedNorm (7 / 4 : ℝ) (actualMomentLockedInnerScaleSource L c) ≤
          C * L ^ 4 ∧
        innerWeightedNorm (7 / 4 : ℝ) (actualMomentLockedInnerPhaseSource L c) ≤
          C * L ^ 4) ∧
      (|actualMomentLockedInnerScaleCharge L c| ≤ C * L ^ 4 ∧
        |actualMomentLockedInnerPhaseCharge L c| ≤ C * L ^ 4) ∧
      (actualMomentLockedInnerScaleCorrectedNorm L c hLp ≤ C * L ^ 4 ∧
        actualMomentLockedInnerPhaseCorrectedNorm L c hLp ≤ C * L ^ 4) ∧
      (actualMomentLockedInnerScaleMoment L c hLp ≤ C * L ^ 4 ∧
        actualMomentLockedInnerPhaseMoment L c hLp ≤ C * L ^ 4) := by
  obtain ⟨A, hA, hInputs⟩ := actual_moment_inner_source_norm_growth
  obtain ⟨K, hK, hCorrections⟩ := actual_fixed_charge_correction_norm_constant
  obtain ⟨D, hD, hMoments⟩ := actual_Hartree_moment_locked_response_fixed_moment_constant
  let C : ℝ := (1 + K + D * K) * A
  have hDK : 0 ≤ D * K := mul_nonneg hD hK
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAC : A ≤ C := by
    calc
      A = 1 * A := by ring
      _ ≤ (1 + K + D * K) * A := mul_le_mul_of_nonneg_right (by linarith) hA
  have hKC : K * A ≤ C :=
    mul_le_mul_of_nonneg_right (show K ≤ 1 + K + D * K by linarith) hA
  have hDKC : (D * K) * A ≤ C :=
    mul_le_mul_of_nonneg_right (show D * K ≤ 1 + K + D * K by linarith) hA
  refine ⟨C, hC, ?_⟩
  intro L c hL hc
  dsimp only
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hPower : 0 ≤ L ^ 4 := pow_nonneg hLp.le _
  have hRaw := hInputs L c hL hc
  have hb := hCorrections (actualMomentLockedInnerScaleSource L c)
    (actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp)
  have hw := hCorrections (actualMomentLockedInnerPhaseSource L c)
    (actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp)
  have hMoment := hMoments L c hLp
  have hBound (x W : ℝ) (hx : x ≤ K * W) (hW : W ≤ A * L ^ 4) :
      x ≤ C * L ^ 4 := by
    calc
      x ≤ K * W := hx
      _ ≤ K * (A * L ^ 4) := mul_le_mul_of_nonneg_left hW hK
      _ = (K * A) * L ^ 4 := by ring
      _ ≤ C * L ^ 4 := mul_le_mul_of_nonneg_right hKC hPower
  have hMomentBound (m n W : ℝ) (hm : m ≤ D * n) (hn : n ≤ K * W)
      (hW : W ≤ A * L ^ 4) : m ≤ C * L ^ 4 := by
    calc
      m ≤ D * n := hm
      _ ≤ D * (K * W) := mul_le_mul_of_nonneg_left hn hD
      _ ≤ D * (K * (A * L ^ 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hK) hD
      _ = ((D * K) * A) * L ^ 4 := by ring
      _ ≤ C * L ^ 4 := mul_le_mul_of_nonneg_right hDKC hPower
  exact ⟨⟨hRaw.1.trans (mul_le_mul_of_nonneg_right hAC hPower),
      hRaw.2.trans (mul_le_mul_of_nonneg_right hAC hPower)⟩,
    ⟨hBound _ _ hb.1 hRaw.1, hBound _ _ hw.2.1 hRaw.2⟩,
    ⟨hBound _ _ hb.2.2.1 hRaw.1, hBound _ _ hw.2.2.2 hRaw.2⟩,
    ⟨hMomentBound _ _ _ hMoment.1 hb.2.2.1 hRaw.1,
      hMomentBound _ _ _ hMoment.2 hw.2.2.2 hRaw.2⟩⟩

end HBL.TypeIIDynamicSelection
