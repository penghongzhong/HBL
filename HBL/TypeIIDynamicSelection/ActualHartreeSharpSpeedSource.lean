import HBL.TypeIIDynamicSelection.ActualHartreeAdjustedSourceNorm
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedProjectionAsymptotics
import HBL.TypeIIDynamicSelection.ActualHartreeNonlocalWeightedQuantitative
import Mathlib.Tactic

/-!
# Sharpening the physical speed-source growth by the actual bubble tail

The crude L^4 growth lost a full power by bounding the actual source
r * eta_L * V_c as an arbitrary radius-L function. Here the real
cutoff satisfies 0 <= eta_L <= 1, the bubble has |r W| <= 1, and its
dilation has uniformly bounded |r Lambda W|. The physical source
profiles differ from those of W by at most M |c|, as already proved.

With L*|c| <= 1 this yields a constant pointwise source bound, and
the ORIGINAL L^{2,7/4}(dr) norm grows at most L^{5/2}. This is a safe
nonoptimal exponent, sufficient for a negative power under a >= L^3.

It does not estimate the original full Kummer obstruction Z and does
not assert nonlinear PDE or profile recursion closure.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

private theorem actual_bubble_two_speed_radial_bounded
    (r : ℝ) (hr : 0 < r) :
    |r * dilationGenerator bubble r| ≤ 3 ∧
      |r * bubble r| ≤ 1 := by
  have hphase : |r * bubble r| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hr.le (bubble_nonneg r))]
    exact radius_mul_bubble_le_one hr.le
  have hscale : |r * dilationGenerator bubble r| ≤ 3 := by
    by_cases hrone : r ≤ 1
    · calc
        |r * dilationGenerator bubble r| =
            r * |dilationGenerator bubble r| := by
              rw [abs_mul, abs_of_pos hr]
        _ ≤ r * 1 :=
          mul_le_mul_of_nonneg_left (actual_moment_bubble_dilation_abs_le_one r) hr.le
        _ ≤ 1 := by simpa using hrone
        _ ≤ 3 := by norm_num
    · have htail := (bubble_two_speed_tail (1 : ℝ) r
        (by norm_num) (by linarith)).2
      have htail' : |r * dilationGenerator bubble r + 1 / 2| ≤ 2 := by
        norm_num at htail ⊢
        exact htail
      calc
        |r * dilationGenerator bubble r| =
            |(r * dilationGenerator bubble r + 1 / 2) + (-1 / 2)| := by
              congr 1
              ring
        _ ≤ |r * dilationGenerator bubble r + 1 / 2| + |-1 / 2| :=
          abs_add_le _ _
        _ ≤ 2 + 1 / 2 := by
          have ht : |-1 / (2 : ℝ)| = 1 / 2 := by norm_num
          rw [ht]
          linarith
        _ ≤ 3 := by norm_num
  exact ⟨hscale, hphase⟩

/-- Source-support bound with the correct L² shell-volume power.
The only input on F is its true pointwise bound and its real support. -/
private theorem actual_inner_constant_supported_source_five_halves
    (L A : ℝ) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (F : ℝ → ℝ) (hF : Measurable F)
    (hBound : ∀ r : ℝ, 0 < r → r ≤ 2 * L → |F r| ≤ A)
    (hFar : ∀ r : ℝ, 2 * L ≤ r → F r = 0) :
    innerWeightedNorm (7 / 4 : ℝ) F ≤ 10 * A * L ^ (5 / 2 : ℝ) := by
  have hLp : 0 < L := by linarith
  let W : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r * F r
  have hW : Measurable W :=
    (affineJapaneseWeight_continuous (7 / 4 : ℝ)).measurable.mul hF
  have hPoint (r : ℝ) (hr : 0 < r) (hrL : r ≤ 2 * L) :
      ‖W r‖ ≤ 5 * A * L ^ 2 := by
    have hw0 : 0 ≤ affineJapaneseWeight (7 / 4 : ℝ) r := by
      unfold affineJapaneseWeight
      positivity
    have hw : affineJapaneseWeight (7 / 4 : ℝ) r ≤ 5 * L ^ 2 := by
      calc
        _ ≤ 1 + r ^ 2 :=
          affineJapaneseWeight_le_one_add_sq (7 / 4 : ℝ) r (by norm_num)
        _ ≤ 5 * L ^ 2 := by
          nlinarith [pow_le_pow_left₀ hr.le hrL 2, sq_nonneg (L - 1)]
    dsimp [W]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    calc
      _ ≤ (5 * L ^ 2) * A :=
        mul_le_mul hw (hBound r hr hrL) (abs_nonneg _) (by positivity)
      _ = 5 * A * L ^ 2 := by ring
  have hZero (r : ℝ) (hr : 2 * L ≤ r) : ‖W r‖ = 0 := by
    simp only [W, hFar r hr, mul_zero, norm_zero]
  have hn := actual_supported_halfLine_L2_norm_le L (5 * A * L ^ 2)
    hLp (by positivity) (fun r => ‖W r‖) hW.norm
      (fun _ => norm_nonneg _) hPoint hZero
  rw [eLpNorm_norm W hW.aestronglyMeasurable] at hn
  change innerWeightedNorm (7 / 4 : ℝ) F ≤
    (5 * A * L ^ 2) * Real.sqrt (2 * L) at hn
  have hSqrt : Real.sqrt (2 * L) ≤ 2 * Real.sqrt L := by
    calc
      _ = Real.sqrt (2 : ℝ) * Real.sqrt L := Real.sqrt_mul (by norm_num) L
      _ ≤ 2 * Real.sqrt L := mul_le_mul_of_nonneg_right
        (by norm_num : Real.sqrt (2 : ℝ) ≤ 2) (Real.sqrt_nonneg L)
  have hPower : L ^ 2 * Real.sqrt L = L ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast L 2, ← Real.rpow_add hLp]
    norm_num
  calc
    _ ≤ (5 * A * L ^ 2) * Real.sqrt (2 * L) := hn
    _ ≤ (5 * A * L ^ 2) * (2 * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hSqrt (by positivity)
    _ = 10 * A * (L ^ 2 * Real.sqrt L) := by ring
    _ = _ := by rw [hPower]

/-- The true moment-locked scale/phase sources have at most L^(5/2)
weighted growth in the actual small-monopole physical region. -/
theorem actual_Hartree_moment_locked_speed_source_five_halves :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L c : ℝ) (hL : 1 ≤ L), L * |c| ≤ 1 →
      innerWeightedNorm (7 / 4 : ℝ) (actualMomentLockedInnerScaleSource L c) ≤
        C * L ^ (5 / 2 : ℝ) ∧
      innerWeightedNorm (7 / 4 : ℝ) (actualMomentLockedInnerPhaseSource L c) ≤
        C * L ^ (5 / 2 : ℝ) := by
  obtain ⟨M, hM, hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  let A : ℝ := 3 + 2 * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨10 * A, by positivity, ?_⟩
  intro L c hL hc
  have hLp : 0 < L := by linarith
  have hMeas := actual_moment_inner_sources_measurable L c
  have hPoint (r : ℝ) (hr : 0 < r) (hrCap : r ≤ 2 * L) :
      |actualMomentLockedInnerScaleSource L c r| ≤ A ∧
      |actualMomentLockedInnerPhaseSource L c r| ≤ A := by
    have hCut := actual_Hartree_inner_source_cutoff_range L r
    have hrc : r * |c| ≤ 2 := by
      calc
        _ ≤ (2 * L) * |c| :=
          mul_le_mul_of_nonneg_right hrCap (abs_nonneg c)
        _ = 2 * (L * |c|) := by ring
        _ ≤ 2 := by linarith only [hc]
    have hErr : r * (M * |c|) ≤ 2 * M := by
      calc
        _ = M * (r * |c|) := by ring
        _ ≤ M * 2 := mul_le_mul_of_nonneg_left hrc hM.le
        _ = 2 * M := by ring
    have hRef := actual_bubble_two_speed_radial_bounded r hr
    have hScale : |r * actualMomentLockedScaleProfile c r| ≤ A := by
      calc
        _ = |r * (actualMomentLockedScaleProfile c r - dilationGenerator bubble r) +
            r * dilationGenerator bubble r| := by congr 1; ring
        _ ≤ |r * (actualMomentLockedScaleProfile c r - dilationGenerator bubble r)| +
            |r * dilationGenerator bubble r| := abs_add_le _ _
        _ ≤ r * (M * |c|) + 3 := by
          rw [abs_mul, abs_of_pos hr]
          exact add_le_add (mul_le_mul_of_nonneg_left (hClose c r hr).1 hr.le) hRef.1
        _ ≤ A := by dsimp [A]; linarith only [hErr]
    have hPhase : |r * actualMomentLockedCore c r| ≤ A := by
      calc
        _ = |r * (actualMomentLockedCore c r - bubble r) + r * bubble r| := by
          congr 1
          ring
        _ ≤ |r * (actualMomentLockedCore c r - bubble r)| + |r * bubble r| :=
          abs_add_le _ _
        _ ≤ r * (M * |c|) + 1 := by
          rw [abs_mul, abs_of_pos hr]
          exact add_le_add (mul_le_mul_of_nonneg_left (hClose c r hr).2 hr.le) hRef.2
        _ ≤ A := by dsimp [A]; linarith only [hErr]
    have hMul (Q : ℝ) (hQ : |r * Q| ≤ A) :
        |r * actualHartreeInnerSourceCutoff L r * Q| ≤ A := by
      have hEq : r * actualHartreeInnerSourceCutoff L r * Q =
          actualHartreeInnerSourceCutoff L r * (r * Q) := by ring
      rw [hEq, abs_mul, abs_of_nonneg hCut.1]
      calc
        _ ≤ 1 * |r * Q| :=
          mul_le_mul_of_nonneg_right hCut.2 (abs_nonneg _)
        _ = |r * Q| := one_mul _
        _ ≤ A := hQ
    exact ⟨hMul _ hScale, hMul _ hPhase⟩
  have hFarScale (r : ℝ) (hr : 2 * L ≤ r) :
      actualMomentLockedInnerScaleSource L c r = 0 :=
    (actual_Hartree_moment_locked_inner_sources_exterior L c r hLp hr).1
  have hFarPhase (r : ℝ) (hr : 2 * L ≤ r) :
      actualMomentLockedInnerPhaseSource L c r = 0 :=
    (actual_Hartree_moment_locked_inner_sources_exterior L c r hLp hr).2.1
  exact ⟨actual_inner_constant_supported_source_five_halves L A hL hA _
      hMeas.1 (fun r hr hrCap => (hPoint r hr hrCap).1) hFarScale,
    actual_inner_constant_supported_source_five_halves L A hL hA _
      hMeas.2 (fun r hr hrCap => (hPoint r hr hrCap).2) hFarPhase⟩

/-- Coupling the genuine inverse estimate with the sharper physical source
growth gives a negative L power whenever a >= L^3. The original complete
Kummer obstruction Z is retained: no unproved residual estimate for Z is
injected into the statement. -/
theorem actual_Hartree_moment_locked_sharp_source_obstruction_gain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L c a B : ℝ) (hL : 1 ≤ L),
        L * |c| ≤ 1 → L ^ 3 ≤ a → 0 < B →
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
              (1024 * C / B ^ 2) * L ^ (-(1 / 2 : ℝ)) * ‖Z‖ := by
  obtain ⟨C, hC, hSharp⟩ :=
    actual_Hartree_moment_locked_speed_source_five_halves
  refine ⟨C, hC, ?_⟩
  intro L c a B hL hc ha hB Fp Fm hp hm db dw Z hSpeed
  dsimp only
  have hLp : 0 < L := by linarith
  have ha0 : 0 < a := (pow_pos hLp 3).trans_le ha
  have hData := hSharp L c hL hc
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  have hGp : innerWeightedNorm (7 / 4 : ℝ) Gp ≤
      C * L ^ (5 / 2 : ℝ) := hData.2
  have hGm : innerWeightedNorm (7 / 4 : ℝ) Gm ≤
      C * L ^ (5 / 2 : ℝ) := hData.1
  have hRaw := actual_Hartree_moment_locked_adjusted_source_norm_bound
    L c hLp Fp Fm hp hm db dw
  have hpBound := mul_le_mul_of_nonneg_left hGp (abs_nonneg dw)
  have hmBound := mul_le_mul_of_nonneg_left hGm (abs_nonneg db)
  have hFactor : 0 ≤ C * L ^ (5 / 2 : ℝ) :=
    mul_nonneg hC.le (Real.rpow_nonneg hLp.le _)
  have hRatio : L ^ (5 / 2 : ℝ) / a ≤ L ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ L ^ (5 / 2 : ℝ) / L ^ 3 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hLp.le _)
          (pow_pos hLp 3) ha
      _ = L ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast L 3, ← Real.rpow_sub hLp]
        norm_num
  have hCoeff : 0 ≤ 1024 * C / B ^ 2 * ‖Z‖ := by positivity
  calc
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm +
        |dw| * innerWeightedNorm (7 / 4 : ℝ) Gp +
        |db| * innerWeightedNorm (7 / 4 : ℝ) Gm := hRaw
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm +
        C * L ^ (5 / 2 : ℝ) * (|db| + |dw|) := by
          nlinarith only [hpBound, hmBound]
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm +
        C * L ^ (5 / 2 : ℝ) * (1024 / (a * B ^ 2) * ‖Z‖) := by
          linarith only [mul_le_mul_of_nonneg_left hSpeed hFactor]
    _ = innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm +
        (1024 * C / B ^ 2 * ‖Z‖) * (L ^ (5 / 2 : ℝ) / a) := by ring
    _ ≤ innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm +
        (1024 * C / B ^ 2 * ‖Z‖) * L ^ (-(1 / 2 : ℝ)) := by
          linarith only [mul_le_mul_of_nonneg_left hRatio hCoeff]
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
