import HBL.TypeIIDynamicSelection.ActualHartreeMovingSelectedGreenMixedDifference
import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingSelectedRegularGreenDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeSlowInnerMovingGreenEndpoint
import Mathlib.Tactic

/-!
# Real moving Hartree Green source plus moving endpoint: a joint derivative

A real Cramer-selected Hartree source F(t,r) and the actual matching
radius r0(t)=ell(t)^(-1/16)/a(t) both vary in time.
The precisely identified cross difference is O(|t-s|*|r0(t)-r0(s)|)
under a visible local Lipschitz budget for the actual Green density.
Its derivative vanishes because the matching radius is differentiable.

The joint derivative is therefore the SUM of the already established
moving-source Green partial derivative and moving-endpoint partial
derivative, WITHOUT separately assuming the mixed derivative vanishes.

The required time-Lipschitz estimate of the original nonlocal
Hartree Green density remains a visible analytic source hypothesis.
There is no prescribed blowup rate, synthetic source or 9/4 claim.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualOriginGreenMovingSelectedCross
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s B t : ℝ) : ℂ :=
  originGreenCoeffB K (r0 t) (F t) B -
    originGreenCoeffB K (r0 s) (F t) B -
    originGreenCoeffB K (r0 t) (F s) B +
    originGreenCoeffB K (r0 s) (F s) B

/-- The mixed moving-source/endpoint term has zero time derivative.
The O(|dt|*|dr|) estimate is DERIVED from the original integral,
not inserted as an arbitrary vanishing-error hypothesis. -/
theorem actual_origin_Green_moving_selected_cross_hasDerivAt_zero
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s B C rdot : ℝ)
    (T : Set ℝ) (hT : T ∈ 𝓝 s)
    (hR : HasDerivAt r0 rdot s)
    (hInt : ∀ t ∈ T,
      IntervalIntegrable (originGreenSourceB K (F t))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceB K (F t))
        volume (r0 s) B ∧
      IntervalIntegrable (originGreenSourceB K (F s))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceB K (F s))
        volume (r0 s) B)
    (hLip : ∀ t ∈ T, ∀ x ∈ uIoc (r0 t) (r0 s),
      ‖originGreenSourceB K (F t) x -
        originGreenSourceB K (F s) x‖ ≤ C * |t-s|) :
    HasDerivAt (actualOriginGreenMovingSelectedCross K F r0 s B) 0 s := by
  have hZero : actualOriginGreenMovingSelectedCross K F r0 s B s = 0 := by
    unfold actualOriginGreenMovingSelectedCross
    abel
  have hRlim : Tendsto (fun t => |r0 s - r0 t|) (𝓝 s) (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℝ => r0 s) (𝓝 s) (𝓝 (r0 s)) :=
      tendsto_const_nhds
    simpa only [sub_self, abs_zero] using
      (hConst.sub hR.continuousAt.tendsto).abs
  have hUpper : Tendsto (fun t => C * |r0 s - r0 t|) (𝓝 s) (𝓝 0) := by
    simpa only [mul_zero] using hRlim.const_mul C
  apply hasDerivAt_iff_tendsto.mpr
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun t =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg (t-s)))
        (norm_nonneg _))
    ?_ hUpper
  filter_upwards [hT] with t ht
  have hBound :=
    actual_origin_Green_moving_source_mixed_difference_Lipschitz
      K F r0 s t B C
      (hInt t ht).1 (hInt t ht).2.1
      (hInt t ht).2.2.1 (hInt t ht).2.2.2
      (hLip t ht)
  change ‖actualOriginGreenMovingSelectedCross K F r0 s B t‖ ≤
    (C * |t-s|) * |r0 s - r0 t| at hBound
  by_cases hEq : t = s
  · subst t
    simp [hZero]
  · have hAbs : 0 < |t-s| := abs_pos.mpr (sub_ne_zero.mpr hEq)
    calc
      ‖t-s‖⁻¹ *
        ‖actualOriginGreenMovingSelectedCross K F r0 s B t -
          actualOriginGreenMovingSelectedCross K F r0 s B s -
          (t-s) • (0 : ℂ)‖ =
        |t-s|⁻¹ * ‖actualOriginGreenMovingSelectedCross K F r0 s B t‖ := by
          simp only [hZero, sub_zero, smul_zero, Real.norm_eq_abs]
      _ ≤ |t-s|⁻¹ * ((C * |t-s|) * |r0 s - r0 t|) :=
        mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr (abs_nonneg _))
      _ = C * |r0 s - r0 t| := by
        field_simp [hAbs.ne']

/-- Source-time and interface-time original Green partial derivatives
compose to the full joint derivative. Only the explicit moving-interval
source-density time Lipschitz hypothesis is additional. -/
theorem actual_origin_Green_moving_selected_joint_hasDerivAt
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ)
    (s B C rdot : ℝ) (T : Set ℝ) (hT : T ∈ 𝓝 s)
    (hR : HasDerivAt r0 rdot s)
    (hInt : ∀ t ∈ T,
      IntervalIntegrable (originGreenSourceB K (F t))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceB K (F t))
        volume (r0 s) B ∧
      IntervalIntegrable (originGreenSourceB K (F s))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceB K (F s))
        volume (r0 s) B)
    (hLip : ∀ t ∈ T, ∀ x ∈ uIoc (r0 t) (r0 s),
      ‖originGreenSourceB K (F t) x -
        originGreenSourceB K (F s) x‖ ≤ C * |t-s|)
    (dSource dEnd : ℂ)
    (hSource : HasDerivAt
      (fun t => originGreenCoeffB K (r0 s) (F t) B) dSource s)
    (hEndpoint : HasDerivAt
      (fun t => originGreenCoeffB K (r0 t) (F s) B) dEnd s) :
    HasDerivAt
      (fun t => originGreenCoeffB K (r0 t) (F t) B)
      (dSource + dEnd) s := by
  have hCross :=
    actual_origin_Green_moving_selected_cross_hasDerivAt_zero
      K F r0 s B C rdot T hT hR hInt hLip
  have hTotal :=
    ((hSource.add hEndpoint).sub
      (hasDerivAt_const s (originGreenCoeffB K (r0 s) (F s) B))).add hCross
  convert hTotal using 1
  · funext t
    simp only [Pi.add_apply, Pi.sub_apply,
      actualOriginGreenMovingSelectedCross]
    abel
  · simp

end HBL.TypeIIDynamicSelection
