import HBL.RadialHartreeBubbleBound
import HBL.HartreeKernelShortRange
import HBL.KinematicTailEstimates
import Mathlib.Tactic

/-!
# Revised HBL 2.13: genuine inverse-square Riesz kernel on bubble-squared source

The already accepted original radial Hartree logarithmic kernel satisfies
  J(r)= int_0^infty rho*K(r,rho)/(1+rho^2) drho <= C0*r.
The old proof drops the crucial far-field radius. Instead split the
**same absolutely integrable positive kernel** at rho=r/2 and rho=2r:
- Near: K(r,rho)<=4rho/r, so the integral <=2.
- Middle: rho/(1+rho^2)<=2/r, and the already constructed unit-radius
  logarithmic mass controls the integral <= 2*unitLogMass.
- Far: K(r,rho)<=4r/rho, so the squared tail is <=2.

Thus J(r)<=4+2*unitLogMass **uniformly in every r>0**.
Together with the original J(r)<=C0*r, this yields
I[bubble^2](r)<=C/(1+r), needed for the FULL mixed Hartree Riesz
spatial potential and positive weighted-Fredholm source gain.

There is no principal-value integral, guessed arctan evaluation,
specially chosen Type-II concentration exponent, or new axiom.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.AffineTail
open HBL.Kinematic

private theorem physical_scalar_radialLog_intervalIntegrable
    (r a b : ℝ) :
    IntervalIntegrable (hartreeRadialLog r) volume a b := by
  apply (splitRadialLog_intervalIntegrable r a b).congr_ae
  apply ae_restrict_of_ae
  filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ r by simp [ae_iff],
    show ∀ᵐ x : ℝ ∂volume, x ≠ -r by simp [ae_iff]] with x hx hx'
  unfold hartreeRadialLog
  rw [radialLog_ratio_eq_sub r x
    (by intro h; apply hx'; linarith)
    (by intro h; apply hx; linarith)]

private theorem physical_scalar_radialLog_scale (r x : ℝ) (hr : 0 < r) :
    hartreeRadialLog r (r * x) = hartreeRadialLog 1 x := by
  unfold hartreeRadialLog
  congr 1
  rw [show r + r * x = r * (1 + x) by ring,
    show r - r * x = r * (1 - x) by ring, abs_mul, abs_of_pos hr]
  exact mul_div_mul_left (1 + x) |1 - x| hr.ne'

private theorem physical_scalar_radialLog_integral_scaled {r : ℝ} (hr : 0 < r) :
    (∫ rho in (0 : ℝ)..(2 * r), hartreeRadialLog r rho) =
      r * radialHartreeUnitLogMass := by
  have hh := intervalIntegral.mul_integral_comp_mul_left
    (f := hartreeRadialLog r) (a := (0 : ℝ)) (b := 2) r
  simpa only [physical_scalar_radialLog_scale r _ hr, mul_zero, mul_comm r 2,
    radialHartreeUnitLogMass] using hh.symm

private theorem physical_scalar_radialLog_nonneg_of_nonneg
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 ≤ rho) :
    0 ≤ hartreeRadialLog r rho := by
  by_cases hp : 0 < rho
  · exact hartreeRadialLog_nonneg r rho hr hp
  · have hzero : rho = 0 := le_antisymm (le_of_not_gt hp) hrho
    subst rho
    unfold hartreeRadialLog
    simp [abs_of_pos hr, hr.ne']

private theorem physical_bubble_sq_eq_inv (rho : ℝ) :
    bubble rho ^ 2 = (1 + rho ^ 2)⁻¹ := by
  unfold bubble
  rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- Unlike the older O(r) estimate, the FULL original absolute-convergent
logarithmic Riesz row against bubble^2 has one uniform finite constant
for every positive radial observation, retaining all diagonal terms. -/
theorem actual_Hartree_bubble_squared_log_row_uniform
    {r : ℝ} (hr : 0 < r) :
    (∫ rho in Ioi (0 : ℝ),
      rho * hartreeRadialLog r rho * bubble rho ^ 2) ≤
      4 + 2 * |radialHartreeUnitLogMass| := by
  let f : ℝ → ℝ :=
    fun rho => rho * hartreeRadialLog r rho * bubble rho ^ 2
  let k : ℝ → ℝ := hartreeRadialLog r
  have hrHalf : 0 < r / 2 := by linarith
  have hrTwo : 0 < 2 * r := by linarith
  have hHalfTwo : r / 2 ≤ 2 * r := by linarith
  have hRow : IntegrableOn f (Ioi (0 : ℝ)) :=
    (radialHartreeBubble_integrable_bound hr).1
  have hNear : IntervalIntegrable f volume 0 (r / 2) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hrHalf.le).2
    exact hRow.mono_set (by intro x hx; exact hx.1)
  have hMiddle : IntervalIntegrable f volume (r / 2) (2 * r) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hHalfTwo).2
    exact hRow.mono_set (by
      intro x hx
      exact lt_of_lt_of_le hrHalf hx.1.le)
  have hFar : IntegrableOn f (Ioi (2 * r)) :=
    hRow.mono_set (by
      intro x hx
      exact lt_trans hrTwo hx)
  have hkNear : IntervalIntegrable k volume 0 (r / 2) :=
    physical_scalar_radialLog_intervalIntegrable r 0 (r / 2)
  have hkMid : IntervalIntegrable k volume (r / 2) (2 * r) :=
    physical_scalar_radialLog_intervalIntegrable r (r / 2) (2 * r)
  have hNearBound :
      (∫ rho in (0 : ℝ)..(r / 2), f rho) ≤ 2 := by
    have hConstant : IntervalIntegrable
        (fun _ : ℝ => (4 / r : ℝ)) volume 0 (r / 2) :=
      continuous_const.intervalIntegrable _ _
    have hPoint (rho : ℝ) (hρ : 0 < rho) (hρh : rho < r / 2) :
        f rho ≤ 4 / r := by
      have hSep : 2 * rho ≤ r := by linarith
      have hK : k rho ≤ 4 * rho / r :=
        hartreeRadialLog_separated_ordered r rho hr hρ hSep
      have hB : rho ^ 2 * bubble rho ^ 2 ≤ 1 := by
        rw [physical_bubble_sq_eq_inv, ← div_eq_mul_inv]
        apply (div_le_iff₀ (by positivity : 0 < 1 + rho ^ 2)).2
        nlinarith [sq_nonneg rho]
      have hB0 : 0 ≤ bubble rho ^ 2 := sq_nonneg _
      dsimp [f]
      calc
        rho * hartreeRadialLog r rho * bubble rho ^ 2 ≤
            rho * (4 * rho / r) * bubble rho ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hK hρ.le) hB0
        _ = (4 / r) * (rho ^ 2 * bubble rho ^ 2) := by ring
        _ ≤ (4 / r) * 1 :=
          mul_le_mul_of_nonneg_left hB (by positivity)
        _ = 4 / r := by ring
    calc
      (∫ rho in (0 : ℝ)..(r / 2), f rho) ≤
          ∫ rho in (0 : ℝ)..(r / 2), (4 / r : ℝ) := by
            apply intervalIntegral.integral_mono_on_of_le_Ioo hrHalf.le
              hNear hConstant
            intro rho hρ
            exact hPoint rho hρ.1 hρ.2
      _ = 2 := by
        rw [intervalIntegral.integral_const]
        field_simp [hr.ne'] <;> simp [hr.ne'] <;> ring
  have hKnearNonneg :
      0 ≤ ∫ rho in (0 : ℝ)..(r / 2), k rho := by
    apply intervalIntegral.integral_nonneg hrHalf.le
    intro rho hρ
    exact physical_scalar_radialLog_nonneg_of_nonneg hr hρ.1
  have hKMidBound :
      (∫ rho in (r / 2)..(2 * r), k rho) ≤
        r * radialHartreeUnitLogMass := by
    have hSplit :=
      intervalIntegral.integral_add_adjacent_intervals hkNear hkMid
    have hFull := physical_scalar_radialLog_integral_scaled hr
    dsimp [k] at hSplit ⊢
    linarith
  have hMiddleBound :
      (∫ rho in (r / 2)..(2 * r), f rho) ≤
        2 * |radialHartreeUnitLogMass| := by
    have hScaled : IntervalIntegrable
        (fun rho : ℝ => (2 / r) * k rho) volume
        (r / 2) (2 * r) := hkMid.const_mul _
    have hPoint (rho : ℝ)
        (hρ : r / 2 < rho) (hρUpper : rho < 2 * r) :
        f rho ≤ (2 / r) * k rho := by
      have hρPos : 0 < rho := hrHalf.trans hρ
      have hk0 : 0 ≤ k rho :=
        hartreeRadialLog_nonneg r rho hr hρPos
      have hWeight : rho * bubble rho ^ 2 ≤ 2 / r := by
        rw [physical_bubble_sq_eq_inv, ← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by positivity : 0 < 1 + rho ^ 2) hr).2
        nlinarith [mul_nonneg hρPos.le
          (show 0 ≤ 2 * rho - r by linarith)]
      dsimp [f]
      calc
        rho * k rho * bubble rho ^ 2 =
            (rho * bubble rho ^ 2) * k rho := by ring
        _ ≤ (2 / r) * k rho :=
          mul_le_mul_of_nonneg_right hWeight hk0
    calc
      (∫ rho in (r / 2)..(2 * r), f rho) ≤
          ∫ rho in (r / 2)..(2 * r), (2 / r) * k rho := by
            apply intervalIntegral.integral_mono_on_of_le_Ioo
              hHalfTwo hMiddle hScaled
            intro rho hρ
            exact hPoint rho hρ.1 hρ.2
      _ = (2 / r) * (∫ rho in (r / 2)..(2 * r), k rho) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ (2 / r) * (r * radialHartreeUnitLogMass) :=
        mul_le_mul_of_nonneg_left hKMidBound (by positivity)
      _ = 2 * radialHartreeUnitLogMass := by
        field_simp [hr.ne'] <;> ring
      _ ≤ 2 * |radialHartreeUnitLogMass| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
  have hFarMajor :
      IntegrableOn
        (fun rho : ℝ => (4 * r) * rho ^ (-2 : ℝ))
        (Ioi (2 * r)) :=
    (integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-2 : ℝ) < -1) hrTwo).const_mul (4 * r)
  have hFarBound :
      (∫ rho in Ioi (2 * r), f rho) ≤ 2 := by
    have hPoint (rho : ℝ) (hρ : 2 * r < rho) :
        f rho ≤ (4 * r) * rho ^ (-2 : ℝ) := by
      have hρpos : 0 < rho := hrTwo.trans hρ
      have hK :
          k rho ≤ 4 * r / rho :=
        (radialLog_far_inv_bound r rho hr hρ.le).2
      have hB : bubble rho ^ 2 ≤ rho ^ (-2 : ℝ) := by
        have hSq : rho ^ (-2 : ℝ) = (rho ^ 2)⁻¹ := by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
            Real.rpow_neg hρpos.le, Real.rpow_natCast]
        rw [physical_bubble_sq_eq_inv, hSq]
        apply one_div_le_one_div_of_le (by positivity : 0 < rho ^ 2)
        nlinarith [sq_nonneg rho]
      have hb0 : 0 ≤ bubble rho ^ 2 := sq_nonneg _
      dsimp [f]
      calc
        rho * k rho * bubble rho ^ 2 ≤
            rho * (4 * r / rho) * bubble rho ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hK hρpos.le) hb0
        _ = (4 * r) * bubble rho ^ 2 := by
          field_simp [hρpos.ne'] <;> ring
        _ ≤ (4 * r) * rho ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
    calc
      (∫ rho in Ioi (2 * r), f rho) ≤
          ∫ rho in Ioi (2 * r), (4 * r) * rho ^ (-2 : ℝ) := by
            apply integral_mono_ae hFar hFarMajor
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hρ
            exact hPoint rho hρ
      _ = (4 * r) * (2 * r)⁻¹ := by
        rw [integral_const_mul, integral_Ioi_rpow_neg_two hrTwo]
      _ = 2 := by
        field_simp [hr.ne']
        ring
  have hSplitMid :=
    intervalIntegral.integral_add_adjacent_intervals hNear hMiddle
  have hSplitFar := intervalIntegral.integral_interval_add_Ioi hRow hFar
  change (∫ rho in Ioi (0 : ℝ), f rho) ≤
      4 + 2 * |radialHartreeUnitLogMass|
  calc
    (∫ rho in Ioi (0 : ℝ), f rho) =
        (∫ rho in (0 : ℝ)..(2 * r), f rho) +
          (∫ rho in Ioi (2 * r), f rho) := hSplitFar.symm
    _ = ((∫ rho in (0 : ℝ)..(r / 2), f rho) +
          (∫ rho in (r / 2)..(2 * r), f rho)) +
          (∫ rho in Ioi (2 * r), f rho) := by rw [hSplitMid]
    _ ≤ 2 + 2 * |radialHartreeUnitLogMass| + 2 := by
      linarith [hNearBound, hMiddleBound, hFarBound]
    _ = 4 + 2 * |radialHartreeUnitLogMass| := by ring

end HBL.TypeIIDynamicSelection
