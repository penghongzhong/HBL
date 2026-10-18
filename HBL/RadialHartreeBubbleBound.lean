import HBL.HartreeKernelShortRange
import HBL.AffineTailLogLocalIntegrability
import HBL.AffineTailLogFarBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A uniform, absolutely convergent radial Riesz row for the actual bubble squared. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Modulation.AffineTail

def radialHartreeUnitLogMass : ℝ :=
  ∫ x in (0 : ℝ)..2, hartreeRadialLog 1 x

def radialHartreeBubbleBoundConstant : ℝ :=
  |radialHartreeUnitLogMass| / 2 + 2 * Real.pi

theorem radialHartreeBubbleBoundConstant_pos : 0 < radialHartreeBubbleBoundConstant := by
  unfold radialHartreeBubbleBoundConstant
  positivity

private theorem bubble_sq (r : ℝ) : bubble r ^ 2 = (1 + r ^ 2)⁻¹ := by
  unfold bubble
  rw [inv_pow, Real.sq_sqrt (by positivity)]

private theorem radialLog_intervalIntegrable (r a b : ℝ) :
    IntervalIntegrable (hartreeRadialLog r) volume a b := by
  apply (splitRadialLog_intervalIntegrable r a b).congr_ae
  apply ae_restrict_of_ae
  filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ r by simp [ae_iff],
    show ∀ᵐ x : ℝ ∂volume, x ≠ -r by simp [ae_iff]] with x hx hx'
  unfold hartreeRadialLog
  rw [radialLog_ratio_eq_sub r x (by intro h; apply hx'; linarith)
    (by intro h; apply hx; linarith)]

private theorem radialLog_scale (r x : ℝ) (hr : 0 < r) :
    hartreeRadialLog r (r * x) = hartreeRadialLog 1 x := by
  unfold hartreeRadialLog
  congr 1
  rw [show r + r * x = r * (1 + x) by ring,
    show r - r * x = r * (1 - x) by ring, abs_mul, abs_of_pos hr]
  exact mul_div_mul_left (1 + x) |1 - x| hr.ne'

private theorem radialLog_integral_scaled {r : ℝ} (hr : 0 < r) :
    (∫ rho in (0 : ℝ)..(2 * r), hartreeRadialLog r rho) =
      r * radialHartreeUnitLogMass := by
  have hh := intervalIntegral.mul_integral_comp_mul_left
    (f := hartreeRadialLog r) (a := (0 : ℝ)) (b := 2) r
  simpa only [radialLog_scale r _ hr, mul_zero, mul_comm r 2,
    radialHartreeUnitLogMass] using hh.symm

/-- The actual positive-half-line logarithmic density against `W²` is integrable,
and its integral is bounded by the radius times a fixed finite constant. -/
theorem radialHartreeBubble_integrable_bound {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho * bubble rho ^ 2) (Ioi 0) ∧
      (∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * bubble rho ^ 2) ≤
        r * radialHartreeBubbleBoundConstant := by
  let f : ℝ → ℝ := fun rho => rho * hartreeRadialLog r rho * bubble rho ^ 2
  have hL := radialLog_intervalIntegrable r 0 (2 * r)
  have hc : Continuous (fun rho : ℝ => rho * bubble rho ^ 2) := by
    simp_rw [bubble_sq]
    fun_prop (discharger := intro; positivity)
  have hlocal : IntervalIntegrable f volume 0 (2 * r) := by
    apply (hL.mul_continuousOn hc.continuousOn).congr_ae
    filter_upwards with rho
    dsimp [f]
    ring
  have hnear : (∫ rho in (0 : ℝ)..(2 * r), f rho) ≤
      r * |radialHartreeUnitLogMass| / 2 := by
    have hcoef (rho : ℝ) : rho * bubble rho ^ 2 ≤ (1 / 2 : ℝ) := by
      rw [bubble_sq, ← div_eq_mul_inv]
      apply (div_le_iff₀ (show 0 < 1 + rho ^ 2 by positivity)).2
      nlinarith [sq_nonneg (rho - 1)]
    calc
      (∫ rho in (0 : ℝ)..(2 * r), f rho) ≤
          ∫ rho in (0 : ℝ)..(2 * r), (1 / 2 : ℝ) * hartreeRadialLog r rho := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) hlocal (hL.const_mul _)
        intro rho hrho
        have hb := mul_le_mul_of_nonneg_right (hcoef rho)
          (hartreeRadialLog_nonneg r rho hr hrho.1)
        simpa only [f, mul_assoc, mul_comm, mul_left_comm] using hb
      _ = r * radialHartreeUnitLogMass / 2 := by
        rw [intervalIntegral.integral_const_mul, radialLog_integral_scaled hr]
        ring
      _ ≤ r * |radialHartreeUnitLogMass| / 2 := by
        gcongr
        exact le_abs_self _
  have hmeas : Measurable f := by
    dsimp [f, hartreeRadialLog, bubble]
    fun_prop
  have hpoint : ∀ rho ∈ Ioi (2 * r), |f rho| ≤ 4 * r * (1 + rho ^ 2)⁻¹ := by
    intro rho hrho
    change 2 * r < rho at hrho
    have hrho0 : 0 < rho := by linarith [hrho]
    obtain ⟨hlog0, hlog⟩ := radialLog_far_inv_bound r rho hr hrho.le
    have hbr : 0 ≤ bubble rho ^ 2 := sq_nonneg _
    rw [show |f rho| = rho * hartreeRadialLog r rho * bubble rho ^ 2 by
      dsimp [f]
      rw [abs_mul, abs_mul, abs_of_pos hrho0, abs_of_nonneg hbr,
        abs_of_nonneg (show 0 ≤ hartreeRadialLog r rho from hlog0)]]
    calc
      rho * hartreeRadialLog r rho * bubble rho ^ 2 ≤
          rho * (4 * r / rho) * bubble rho ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hrho0.le) hbr
      _ = _ := by
        rw [bubble_sq]
        field_simp
  have hmajor : IntegrableOn (fun rho : ℝ => 4 * r * (1 + rho ^ 2)⁻¹) (Ioi (2 * r)) :=
    (integrable_inv_one_add_sq.const_mul (4 * r)).integrableOn
  have hfar : IntegrableOn f (Ioi (2 * r)) := by
    apply hmajor.mono' hmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    exact hpoint rho hrho
  have htail : (∫ rho in Ioi (2 * r), f rho) ≤ 2 * Real.pi * r := by
    calc
      (∫ rho in Ioi (2 * r), f rho) ≤
          ∫ rho in Ioi (2 * r), 4 * r * (1 + rho ^ 2)⁻¹ := by
        apply integral_mono_ae hfar hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
        exact (le_abs_self _).trans (hpoint rho hrho)
      _ = 4 * r * (Real.pi / 2 - Real.arctan (2 * r)) := by
        rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
      _ ≤ 2 * Real.pi * r := by
        have ha : 0 ≤ Real.arctan (2 * r) := Real.arctan_nonneg.mpr (by positivity)
        nlinarith [mul_nonneg hr.le ha]
  have hlocalSet : IntegrableOn f (Ioc 0 (2 * r)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 hlocal
  have hset : Ioc (0 : ℝ) (2 * r) ∪ Ioi (2 * r) = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx, _⟩ | hx) <;> linarith
    · intro hx
      by_cases hh : x ≤ 2 * r
      · exact Or.inl ⟨hx, hh⟩
      · exact Or.inr (lt_of_not_ge hh)
  have htotal : IntegrableOn f (Ioi 0) := by
    rw [← hset]
    exact hlocalSet.union hfar
  refine ⟨htotal, ?_⟩
  have hsplit := intervalIntegral.integral_interval_add_Ioi htotal hfar
  change (∫ rho in Ioi (0 : ℝ), f rho) ≤ _
  calc
    (∫ rho in Ioi (0 : ℝ), f rho) =
        (∫ rho in (0 : ℝ)..(2 * r), f rho) + ∫ rho in Ioi (2 * r), f rho := hsplit.symm
    _ ≤ r * |radialHartreeUnitLogMass| / 2 + 2 * Real.pi * r := add_le_add hnear htail
    _ = _ := by unfold radialHartreeBubbleBoundConstant; ring

end HBL.Modulation.AffineTail
