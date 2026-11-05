import HBL.TypeIIDynamicSelection.ActualHartreeMatchedExteriorTail

/-!
The corrected exterior RHS is the original full RHS minus the SAME two
moment-locked speed sources. Its inverse-square envelope costs a*B times
the real speed increment, not a^2. The bubble-tail and actual-profile
closeness producers are reused; no new inverse or free charge is introduced.
Positive-radius continuity is recovered from the already proved continuous
radially conjugated sources on a local cutoff plateau.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- Reuse continuous conjugated sources to obtain the actual uncut speed
profiles' continuity at every strictly positive physical radius. -/
theorem actual_Hartree_speed_profiles_continuousAt
    (c t : ℝ) (ht : 0 < t) :
    ContinuousAt (actualMomentLockedScaleProfile c) t ∧
      ContinuousAt (actualMomentLockedCore c) t := by
  have hR : 0 < 2 * t := by positivity
  have hSources := actual_Hartree_moment_locked_inner_sources_continuous (2 * t) c
  have heqS : actualMomentLockedScaleProfile c =ᶠ[𝓝 t]
      (fun y => actualMomentLockedInnerScaleSource (2 * t) c y / y) := by
    filter_upwards [Ioo_mem_nhds ht (by linarith : t < 2 * t)] with y hy
    have hCut := actual_Hartree_inner_source_cutoff_one (2 * t) y hR hy.2.le
    simp only [actualMomentLockedInnerScaleSource, hCut, mul_one]
    field_simp [hy.1.ne']
  have heqP : actualMomentLockedCore c =ᶠ[𝓝 t]
      (fun y => actualMomentLockedInnerPhaseSource (2 * t) c y / y) := by
    filter_upwards [Ioo_mem_nhds ht (by linarith : t < 2 * t)] with y hy
    have hCut := actual_Hartree_inner_source_cutoff_one (2 * t) y hR hy.2.le
    simp only [actualMomentLockedInnerPhaseSource, hCut, mul_one]
    field_simp [hy.1.ne']
  exact ⟨(continuousAt_congr heqS).2
      (hSources.1.continuousAt.div continuousAt_id ht.ne'),
    (continuousAt_congr heqP).2
      (hSources.2.continuousAt.div continuousAt_id ht.ne')⟩

/-- Source regularity of the actual corrected exterior forcing, derived
from regularity of the original RHS, not assumed for every speed pair. -/
theorem actual_Hartree_corrected_outer_source_continuousAt
    (a c db dw r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (F : ℝ → ℂ) (hF : ContinuousAt F r) :
    ContinuousAt (fun x => F x -
      (db : ℂ) * actualMomentLockedScaledScaleSource a c x -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c x) r := by
  have hProfiles := actual_Hartree_speed_profiles_continuousAt c (a * r) (mul_pos ha hr)
  have hArg : ContinuousAt (fun x : ℝ => a * x) r :=
    continuousAt_const.mul continuousAt_id
  have hScale : ContinuousAt (actualMomentLockedScaledScaleSource a c) r :=
    continuousAt_const.mul (continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (hProfiles.1.comp hArg)))
  have hPhase : ContinuousAt (actualMomentLockedScaledPhaseSource a c) r :=
    continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (hProfiles.2.comp hArg))
  exact (hF.sub (continuousAt_const.mul hScale)).sub
    (continuousAt_const.mul hPhase)

/-- Both true scaled speed directions have a common inverse-square
majorant whose coefficient is only O(a B). The constant precedes all
physical parameters; a|c|<=1 and B<=1 control the actual monopole part. -/
theorem actual_Hartree_scaled_speed_outer_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ (L c a B : ℝ),
      1 ≤ L → 0 < a → B ≤ 1 → a * |c| ≤ 1 →
      ∀ r ∈ Icc (L / a) B,
        ‖actualMomentLockedScaledScaleSource a c r‖ ≤ C * a * B / r ^ 2 ∧
        ‖actualMomentLockedScaledPhaseSource a c r‖ ≤ C * a * B / r ^ 2 := by
  obtain ⟨M, hM, hClose⟩ := actual_Hartree_moment_locked_speed_profiles_uniform_close
  refine ⟨M + 3, by linarith, ?_⟩
  intro L c a B hL ha hB hSmall r hr
  have hLp : 0 < L := by linarith
  have hrp : 0 < r := (div_pos hLp ha).trans_le hr.1
  have htL : L ≤ a * r := by
    have h := (div_le_iff₀ ha).1 hr.1
    simpa only [mul_comm] using h
  have ht : 0 < a * r := mul_pos ha hrp
  have htOne : 1 ≤ a * r := hL.trans htL
  have htc : (a * r) * |c| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hSmall hrp.le
    nlinarith only [h, hr.2, hB]
  have hTail := bubble_two_speed_tail 1 (a * r) (by norm_num) htOne
  norm_num only [one_pow, div_one] at hTail
  have hScaleRef : |(a * r) * dilationGenerator bubble (a * r)| ≤ 3 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hTail.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hPhaseRef : |(a * r) * bubble (a * r)| ≤ 3 := by
    rw [abs_of_nonneg (mul_nonneg ht.le (bubble_nonneg _))]
    exact (radius_mul_bubble_le_one ht.le).trans (by norm_num)
  have hProfile (P P0 : ℝ) (href : |(a * r) * P0| ≤ 3)
      (hclose : |P - P0| ≤ M * |c|) : |(a * r) * P| ≤ M + 3 := by
    calc
      _ = |(a * r) * (P - P0) + (a * r) * P0| := by congr 1; ring
      _ ≤ |(a * r) * (P - P0)| + |(a * r) * P0| := abs_add_le _ _
      _ ≤ (a * r) * (M * |c|) + 3 := by
        rw [abs_mul, abs_of_pos ht]
        exact add_le_add (mul_le_mul_of_nonneg_left hclose ht.le) href
      _ ≤ M + 3 := by
        nlinarith only [mul_le_mul_of_nonneg_left htc hM.le]
  have hScaled (P : ℝ) (hP : |(a * r) * P| ≤ M + 3) :
      a ^ 2 * |P| ≤ (M + 3) * a * B / r ^ 2 := by
    apply (le_div_iff₀ (pow_pos hrp 2)).2
    rw [abs_mul, abs_of_pos ht] at hP
    calc
      _ = (a * r) * ((a * r) * |P|) := by ring
      _ ≤ (a * r) * (M + 3) := mul_le_mul_of_nonneg_left hP ht.le
      _ ≤ (M + 3) * a * B := by
        nlinarith only [mul_le_mul_of_nonneg_left hr.2
          (show 0 ≤ (M + 3) * a by positivity)]
  constructor
  · simpa only [actualMomentLockedScaledScaleSource, actualMomentLockedScaleSource,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg a)] using
      hScaled _ (hProfile _ _ hScaleRef (hClose c (a * r) ht).1)
  · simpa only [actualMomentLockedScaledPhaseSource, actualMomentLockedPhaseSource,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)] using
      hScaled _ (hProfile _ _ hPhaseRef (hClose c (a * r) ht).2)

/-- The exact corrected outer RHS retains the full source and the two
actual speeds; the output envelope is explicit and homogeneous. -/
theorem actual_Hartree_corrected_outer_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ (L c a B : ℝ),
      1 ≤ L → 0 < a → B ≤ 1 → a * |c| ≤ 1 →
      ∀ (F : ℝ → ℂ) (Q db dw : ℝ),
        (∀ r ∈ Icc (L / a) B, ‖F r‖ ≤ Q / r ^ 2) →
        ∀ r ∈ Icc (L / a) B,
          ‖F r - (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
              (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r‖ ≤
            (Q + C * a * B * (|db| + |dw|)) / r ^ 2 := by
  obtain ⟨C, hC, hSpeed⟩ := actual_Hartree_scaled_speed_outer_envelope
  refine ⟨C, hC, ?_⟩
  intro L c a B hL ha hB hSmall F Q db dw hF r hr
  have hS := hSpeed L c a B hL ha hB hSmall r hr
  calc
    _ ≤ (‖F r‖ + ‖(db : ℂ) * actualMomentLockedScaledScaleSource a c r‖) +
        ‖(dw : ℂ) * actualMomentLockedScaledPhaseSource a c r‖ :=
      (norm_sub_le _ _).trans (_root_.add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖F r‖ + |db| * ‖actualMomentLockedScaledScaleSource a c r‖ +
        |dw| * ‖actualMomentLockedScaledPhaseSource a c r‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Q / r ^ 2 + |db| * (C * a * B / r ^ 2) +
        |dw| * (C * a * B / r ^ 2) :=
      add_le_add (add_le_add (hF r hr)
        (mul_le_mul_of_nonneg_left hS.1 (abs_nonneg db)))
        (mul_le_mul_of_nonneg_left hS.2 (abs_nonneg dw))
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
