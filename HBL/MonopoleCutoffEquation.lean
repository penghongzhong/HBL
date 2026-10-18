import HBL.MonopoleCutoffLeakage

/-! The actual half-line equation and core defect of the truncated monopole. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole

open HBL.Modulation.AffineTail

/-- The actual inner truncation of the conjugated monopole profile. -/
def monopoleInnerProfile (R r : ℝ) : ℝ :=
  (1 - cutoff (r / R)) * monopoleProfile r

private theorem monopoleProfile_kernel_integrable {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun rho => hartreeKernel r rho * monopoleProfile rho) (Ioi 0) := by
  have hl := nonlocalApply_integrable_of_weighted_memLp
    monopoleLogModel weightedLogModel_memLp_two hr
  have ha := nonlocalApply_integrable_of_weighted_memLp
    model weightedAffineModel_memLp_two hr
  have hh := nonlocalApply_integrable_of_weighted_memLp
    monopoleRemainder monopoleRemainder_weighted_memLp_two hr
  refine ((hl.add (ha.const_mul monopoleAffineSlope)).add hh).congr ?_
  filter_upwards with rho
  simp only [Pi.add_apply]
  unfold monopoleProfile
  ring

/-- On the core, the entire linear defect is the genuine nonlocal outer tail. -/
theorem monopoleInnerProfile_hPlus_core
    {R r : ℝ} (hR : 4 ≤ R) (hr : 0 < r) (hsep : r ≤ R / 2) :
    hPlusApply (monopoleInnerProfile R) r =
      monopoleSource r + nonlocalApply (monopoleOuterTail R) r := by
  have hR0 : 0 < R := by linarith
  have hrR : r < R := by linarith
  have he : monopoleInnerProfile R =ᶠ[𝓝 r] monopoleProfile := by
    filter_upwards [Iio_mem_nhds hrR] with x hx
    have hxR : x / R ≤ 1 := (div_le_one hR0).2 hx.le
    simp only [monopoleInnerProfile, cutoff_zero_of_le_one _ hxR, sub_zero, one_mul]
  have ht := (monopoleOuterTail_nonlocal_control hR hr hsep).1
  have hp := monopoleProfile_kernel_integrable hr.le
  have hn : nonlocalApply (monopoleInnerProfile R) r =
      nonlocalApply monopoleProfile r - nonlocalApply (monopoleOuterTail R) r := by
    unfold nonlocalApply
    rw [← integral_sub hp ht]
    congr 1
    funext rho
    unfold monopoleInnerProfile monopoleOuterTail
    ring
  calc
    hPlusApply (monopoleInnerProfile R) r =
        hPlusApply monopoleProfile r + nonlocalApply (monopoleOuterTail R) r := by
      unfold hPlusApply
      rw [he.deriv.deriv_eq, he.eq_of_nhds, hn]
      ring
    _ = _ := by rw [monopoleProfile_hPlus_equation hr]

/-- The real half-line operator has an explicit quadratic-radius core defect. -/
theorem monopoleInnerProfile_hPlus_core_abs_le
    {R r : ℝ} (hR : 4 ≤ R) (hr : 0 < r) (hsep : r ≤ R / 2) :
    |hPlusApply (monopoleInnerProfile R) r - monopoleSource r| ≤
      16 * Real.pi * hartreeKappa * monopoleLinearGrowthConstant *
        r * bubble r ^ 3 / R ^ 2 := by
  rw [monopoleInnerProfile_hPlus_core hR hr hsep, add_sub_cancel_left]
  exact (monopoleOuterTail_nonlocal_control hR hr hsep).2

end HBL.Modulation.Monopole
