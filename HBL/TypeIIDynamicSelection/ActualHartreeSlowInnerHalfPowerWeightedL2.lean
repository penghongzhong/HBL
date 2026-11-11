import HBL.TypeIIDynamicSelection.ActualHartreeSlowInnerHalfPowerSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
The same full nonlocal quartic-Hartree inner forcing has a squared
weighted-L2 bound of actual length order ell^(1/2). No additional source
envelope, prescribed time order, or blowup law is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- The true, radially conjugated and cutoff original ten-term Hartree
source has weighted squared norm bounded by K(B,A)^2 ell times a fixed
integrable tail, without taking any independent source-size hypothesis. -/
theorem actual_Hartree_slow_inner_half_power_weighted_L2
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let G : ℝ → ℂ := actualHartreeRadiallyConjugatedInnerSource
      (actualHartreeSlowInnerRadius ell) ell c z
    MemLp (fun r => affineJapaneseWeight (7 / 4 : ℝ) r * ‖G r‖)
      2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ),
      (affineJapaneseWeight (7 / 4 : ℝ) r * ‖G r‖) ^ 2) ≤
      (actualHartreeSlowInnerHalfPowerConstant B A) ^ 2 * ell *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 2 : ℝ))) := by
  let R : ℝ := actualHartreeSlowInnerRadius ell
  let G : ℝ → ℂ := actualHartreeRadiallyConjugatedInnerSource R ell c z
  let K : ℝ := actualHartreeSlowInnerHalfPowerConstant B A
  let S : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r * ‖G r‖
  have hR : 0 < R := Real.rpow_pos_of_pos hell _
  have hOld := actual_Hartree_conjugated_localized_inner_weighted
    R ell c B A hR hell hellOne hc hB hA z hz hSup hStrauss
  have hG : Measurable G := hOld.1
  have hSm : Measurable S :=
    (affineJapaneseWeight_continuous (7 / 4 : ℝ)).measurable.mul hG.norm
  have hS0 (r : ℝ) : 0 ≤ S r := by
    dsimp [S, affineJapaneseWeight]
    positivity
  have hPoint (r : ℝ) (hr : 0 < r) :
      S r ≤ K * Real.sqrt ell * (1 + r) ^ (-(5 / 4 : ℝ)) := by
    exact actual_Hartree_conjugated_slow_inner_half_power_pointwise
      ell c B A hell hellOne hc hB hA z hz hSup hStrauss r hr
  have hTail : IntegrableOn
      (fun r : ℝ => (1 + r) ^ (-(5 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
    simpa only [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt
        (show -(5 / 2 : ℝ) < -1 by norm_num)
        (show -(1 : ℝ) < 0 by norm_num))
  have hMajor : IntegrableOn
      (fun r : ℝ => (K * Real.sqrt ell) ^ 2 *
        (1 + r) ^ (-(5 / 2 : ℝ))) (Ioi (0 : ℝ)) :=
    hTail.const_mul ((K * Real.sqrt ell) ^ 2)
  have hSq (r : ℝ) (hr : 0 < r) :
      S r ^ 2 ≤ (K * Real.sqrt ell) ^ 2 *
        (1 + r) ^ (-(5 / 2 : ℝ)) := by
    have hp := pow_le_pow_left₀ (hS0 r) (hPoint r hr) 2
    have hd : 0 ≤ (1 : ℝ) + r := by linarith
    have hPower : ((1 + r) ^ (-(5 / 4 : ℝ))) ^ 2 =
        (1 + r) ^ (-(5 / 2 : ℝ)) := by
      calc
        _ = ((1 + r) ^ (-(5 / 4 : ℝ))) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (1 + r) ^ (-(5 / 4 : ℝ) * 2) :=
          (Real.rpow_mul hd (-(5 / 4 : ℝ)) 2).symm
        _ = _ := by norm_num
    simpa only [mul_pow, hPower] using hp
  have hInt : IntegrableOn (fun r : ℝ => S r ^ 2) (Ioi (0 : ℝ)) := by
    apply hMajor.mono' (hSm.pow_const 2).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S r))]
    exact hSq r hr
  have hLp : MemLp S 2 halfLineMeasure := hOld.2.1
  have hEll : (Real.sqrt ell) ^ 2 = ell := Real.sq_sqrt hell.le
  change MemLp S 2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
      K ^ 2 * ell *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 2 : ℝ)))
  refine ⟨hLp, ?_⟩
  calc
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
        ∫ r in Ioi (0 : ℝ), (K * Real.sqrt ell) ^ 2 *
          (1 + r) ^ (-(5 / 2 : ℝ)) := by
      apply integral_mono_ae hInt hMajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hSq r hr
    _ = (K * Real.sqrt ell) ^ 2 *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 2 : ℝ))) := by
      rw [integral_const_mul]
    _ = K ^ 2 * ell *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 2 : ℝ))) := by
      rw [mul_pow, hEll]

end HBL.TypeIIDynamicSelection
