import HBL.MonopoleProfileEquation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The genuine radial Riesz potential of bounded compactly supported densities. -/

noncomputable section
open Set MeasureTheory

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The radial Riesz potential with the manuscript's actual normalization. -/
def radialHartreePotential (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 * Real.pi * hartreeKappa / r) *
    ∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * F rho

/-- Absolute convergence follows from measurable bounded compact support,
via the proved weighted Hartree row estimate. -/
theorem radialHartreePotential_integrable
    (F : ℝ → ℝ) (hf : Measurable F) (hcomp : HasCompactSupport F)
    {M : ℝ} (hbound : ∀ rho : ℝ, |F rho| ≤ M) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi (0 : ℝ)) := by
  let d : ℝ → ℝ := fun rho => weightedGreenDecay rho * rho / bubble rho ^ 3
  have hd : Continuous d := by
    unfold d weightedGreenDecay bubble
    fun_prop (discharger := intro; positivity)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hd.continuousOn
  have hprodcomp : HasCompactSupport (fun rho => d rho * F rho) := hcomp.mul_left
  have hprod : ∀ rho, ‖d rho * F rho‖ ≤ max C 0 * max M 0 := by
    intro rho
    by_cases hh : rho ∈ tsupport F
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul ((hC rho hh).trans (le_max_left _ _))
        ((hbound rho).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hh, mul_zero, norm_zero]
      exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hw : MemLp (fun rho => d rho * F rho) 2 halfLineMeasure :=
    hprodcomp.memLp_of_bound ((hd.measurable.mul hf).aestronglyMeasurable)
      (max C 0 * max M 0) (Filter.Eventually.of_forall hprod)
  have hq : MemLp (fun rho => weightedGreenDecay rho *
      (rho * F rho / bubble rho ^ 3)) 2 halfLineMeasure := by
    convert hw using 1
    funext rho
    dsimp [d]
    ring
  have hint := nonlocalApply_integrable_of_weighted_memLp
    (fun rho => rho * F rho / bubble rho ^ 3) hq hr.le
  have hc : 8 * Real.pi * hartreeKappa * bubble r ^ 3 ≠ 0 := by
    unfold hartreeKappa bubble
    positivity
  refine (hint.const_mul (8 * Real.pi * hartreeKappa * bubble r ^ 3)⁻¹).congr ?_
  filter_upwards with rho
  have hb : bubble rho ≠ 0 := by unfold bubble; positivity
  unfold hartreeKernel hartreeRadialLog
  have he : 8 * Real.pi * hartreeKappa * bubble r ^ 3 * bubble rho ^ 3 *
      Real.log ((r + rho) / |r - rho|) * (rho * F rho / bubble rho ^ 3) =
      (8 * Real.pi * hartreeKappa * bubble r ^ 3) *
        (rho * Real.log ((r + rho) / |r - rho|) * F rho) := by
    field_simp
  rw [he, inv_mul_cancel_left₀ hc]

end HBL.Modulation.Monopole
