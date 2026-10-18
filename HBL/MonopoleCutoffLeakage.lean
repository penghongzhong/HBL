import HBL.MonopoleProfileEquation
import HBL.HartreeTailLeakage

/-! Actual far-field cutoff of the constructed monopole and its inner Hartree leakage. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

def monopoleLinearGrowthConstant : ℝ :=
  1 + |monopoleAffineSlope| + weightedGreenPrimitiveBound monopoleTotalDatum

def monopoleOuterTail (R rho : ℝ) : ℝ :=
  cutoff (rho / R) * monopoleProfile rho

theorem monopoleLinearGrowthConstant_pos : 0 < monopoleLinearGrowthConstant := by
  have hB := weightedGreenPrimitiveBound_nonneg monopoleTotalDatum
  unfold monopoleLinearGrowthConstant
  positivity

theorem monopoleProfile_linear_growth {rho : ℝ} (hrho : 4 ≤ rho) :
    |monopoleProfile rho| ≤ monopoleLinearGrowthConstant * rho := by
  have hrho0 : 0 < rho := by linarith
  have hm : model rho = rho := model_eq_id_of_two_le rho (by linarith)
  have hl : |monopoleLogModel rho| ≤ rho := by
    simpa only [hm] using monopoleLogModel_abs_le_model rho
  have hrem := monopoleRemainder_abs_le hrho0
  have hB := weightedGreenPrimitiveBound_nonneg monopoleTotalDatum
  calc
    |monopoleProfile rho| ≤ |monopoleLogModel rho| +
        |monopoleAffineSlope * model rho| + |monopoleRemainder rho| := by
      unfold monopoleProfile
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ rho + |monopoleAffineSlope| * rho +
        weightedGreenPrimitiveBound monopoleTotalDatum := by
      rw [abs_mul, hm, abs_of_pos hrho0]
      linarith
    _ ≤ monopoleLinearGrowthConstant * rho := by
      unfold monopoleLinearGrowthConstant
      nlinarith

private theorem monopoleOuterTail_zero {R rho : ℝ} (hR : 0 < R) (hrho : rho ≤ R) :
    monopoleOuterTail R rho = 0 := by
  unfold monopoleOuterTail
  rw [cutoff_zero_of_le_one (rho / R) ((div_le_one hR).mpr hrho), zero_mul]

/-- The actual cutoff tail is integrable against each inner kernel row, and its
nonlocal contribution is quantitatively `O(R⁻²)`. No profile growth or kernel
integrability assumption occurs in this terminal theorem. -/
theorem monopoleOuterTail_nonlocal_control {R r : ℝ}
    (hR : 4 ≤ R) (hr : 0 < r) (hsep : r ≤ R / 2) :
    IntegrableOn (fun rho => hartreeKernel r rho * monopoleOuterTail R rho) (Ioi 0) ∧
      |nonlocalApply (monopoleOuterTail R) r| ≤
        16 * Real.pi * hartreeKappa * monopoleLinearGrowthConstant * r * bubble r ^ 3 / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hc : Continuous (monopoleOuterTail R) :=
    (cutoff_contDiff_infty.continuous.comp (continuous_id.div_const R)).mul
      monopoleProfile_continuous
  have hb : ∀ rho, R ≤ rho → |monopoleOuterTail R rho| ≤ monopoleLinearGrowthConstant * rho := by
    intro rho hrho
    unfold monopoleOuterTail
    rw [abs_mul, abs_of_nonneg (show 0 ≤ cutoff (rho / R) from Real.smoothTransition.nonneg _)]
    calc
      cutoff (rho / R) * |monopoleProfile rho| ≤ 1 * |monopoleProfile rho| :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (abs_nonneg _)
      _ ≤ monopoleLinearGrowthConstant * rho := by
        simpa only [one_mul] using monopoleProfile_linear_growth (hR.trans hrho)
  have ht := hartree_tail_linear_bound (monopoleOuterTail R) hc.measurable
    monopoleLinearGrowthConstant_pos.le hr hR0 (by linarith) hb
  let f : ℝ → ℝ := fun rho => hartreeKernel r rho * monopoleOuterTail R rho
  have he : f = (Ioi R).indicator f := by
    funext rho
    by_cases hh : rho ∈ Ioi R
    · rw [indicator_of_mem hh]
    · rw [indicator_of_notMem hh]
      simp only [f, monopoleOuterTail_zero hR0 (le_of_not_gt hh), mul_zero]
  have hi : IntegrableOn ((Ioi R).indicator f) (Ioi 0) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi]
    change Integrable f ((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi R))
    rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hR0.le)]
    exact ht.1
  have hfull : IntegrableOn f (Ioi 0) :=
    hi.congr_fun (fun rho _ => congrFun he.symm rho) measurableSet_Ioi
  refine ⟨hfull, ?_⟩
  have heint : (∫ rho in Ioi (0 : ℝ), f rho) = ∫ rho in Ioi R, f rho := by
    calc
      (∫ rho in Ioi (0 : ℝ), f rho) = ∫ rho in Ioi (0 : ℝ), (Ioi R).indicator f rho := by
        exact integral_congr_ae (Eventually.of_forall (fun rho => congrFun he rho))
      _ = _ := by
        rw [integral_indicator measurableSet_Ioi,
          Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hR0.le)]
  change |∫ rho in Ioi (0 : ℝ), f rho| ≤ _
  rw [heint]
  exact ht.2

end HBL.Modulation.Monopole
