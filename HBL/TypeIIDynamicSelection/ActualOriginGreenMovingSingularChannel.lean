import HBL.TypeIIDynamicSelection.ActualHartreeMovingGreenJointDerivative
import HBL.TypeIIDynamicSelection.ActualOriginGreenMovingEndpointDerivative
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic

/-!
# The singular origin-Kummer Green channel with one moving Hartree source

These are the source, endpoint, and mixed derivative identities for the
ORIGINAL outgoing singular coefficient. They are the missing dual of
the already audited regular Green coefficient results. Every integrability
and derivative majorant is explicit; no PDE time rate is postulated.

All formulas use the same original Wronskian and source. This file is
not the full moving four-region nonlinear Hartree PDE construction.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology Interval

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Uniform argument order for the original singular coefficient:
the actual A_K(r) integrates from r to the fixed upper interface. -/
def actualSingularGreenCoeff
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 : ℝ) (F : ℝ → ℂ) (B : ℝ) : ℂ :=
  originGreenCoeffA K B F r0

theorem actual_origin_SingularGreen_coeff_fixed_lower_source_hasDerivAt
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 B s : ℝ)
    (F Fdot : ℝ → ℝ → ℂ)
    (S : Set ℝ) (bound : ℝ → ℝ)
    (hS : S ∈ 𝓝 s)
    (hMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (originGreenSourceA K (F t)) (volume.restrict (Ι r0 B)))
    (hInt : IntervalIntegrable
      (originGreenSourceA K (F s)) volume r0 B)
    (hDotMeas : AEStronglyMeasurable
      (originGreenSourceA K (Fdot s)) (volume.restrict (Ι r0 B)))
    (hBound : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ S, ‖originGreenSourceA K (Fdot t) r‖ ≤ bound r)
    (hBoundInt : IntervalIntegrable bound volume r0 B)
    (hSourceDeriv : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ S, HasDerivAt (fun tau => F tau r) (Fdot t r) t) :
    HasDerivAt
      (fun t => actualSingularGreenCoeff K r0 (F t) B)
      (actualSingularGreenCoeff K r0 (Fdot s) B) s := by
  have hDiff : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ S,
        HasDerivAt
          (fun tau => originGreenSourceA K (F tau) r)
          (originGreenSourceA K (Fdot t) r) t := by
    filter_upwards [hSourceDeriv] with r hr
    intro hrmem t ht
    have hd := hr hrmem t ht
    have hm :=
      hd.mul_const
        (originPhysicalValue K.x r / originGreenWronskian K r)
    simpa only [originGreenSourceA, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hm
  have hParam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) hS hMeas hInt hDotMeas hBound hBoundInt hDiff
  unfold actualSingularGreenCoeff originGreenCoeffA
  exact hParam.2


theorem actual_origin_SingularGreen_moving_source_mixed_difference_exact
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s t B : ℝ)
    (htShort : IntervalIntegrable (originGreenSourceA K (F t))
      volume (r0 t) (r0 s))
    (htLong : IntervalIntegrable (originGreenSourceA K (F t))
      volume (r0 s) B)
    (hsShort : IntervalIntegrable (originGreenSourceA K (F s))
      volume (r0 t) (r0 s))
    (hsLong : IntervalIntegrable (originGreenSourceA K (F s))
      volume (r0 s) B) :
    actualSingularGreenCoeff K (r0 t) (F t) B -
      actualSingularGreenCoeff K (r0 s) (F t) B -
      actualSingularGreenCoeff K (r0 t) (F s) B +
      actualSingularGreenCoeff K (r0 s) (F s) B =
      ∫ x in (r0 t)..(r0 s),
        (originGreenSourceA K (F t) x -
          originGreenSourceA K (F s) x) := by
  have htSplit :
      actualSingularGreenCoeff K (r0 t) (F t) B =
        (∫ x in (r0 t)..(r0 s), originGreenSourceA K (F t) x) +
          actualSingularGreenCoeff K (r0 s) (F t) B := by
    exact (intervalIntegral.integral_add_adjacent_intervals htShort htLong).symm
  have hsSplit :
      actualSingularGreenCoeff K (r0 t) (F s) B =
        (∫ x in (r0 t)..(r0 s), originGreenSourceA K (F s) x) +
          actualSingularGreenCoeff K (r0 s) (F s) B := by
    exact (intervalIntegral.integral_add_adjacent_intervals hsShort hsLong).symm
  rw [htSplit, hsSplit, intervalIntegral.integral_sub htShort hsShort]
  abel

/-- Exact upper bound for the cross effect of changing the physical
Hartree source while the real lower interface moves.  No order
assumption on r0(t) versus r0(s) is needed. -/
theorem actual_origin_SingularGreen_moving_source_mixed_difference_Lipschitz
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s t B C : ℝ)
    (htShort : IntervalIntegrable (originGreenSourceA K (F t))
      volume (r0 t) (r0 s))
    (htLong : IntervalIntegrable (originGreenSourceA K (F t))
      volume (r0 s) B)
    (hsShort : IntervalIntegrable (originGreenSourceA K (F s))
      volume (r0 t) (r0 s))
    (hsLong : IntervalIntegrable (originGreenSourceA K (F s))
      volume (r0 s) B)
    (hLip : ∀ x ∈ uIoc (r0 t) (r0 s),
      ‖originGreenSourceA K (F t) x -
        originGreenSourceA K (F s) x‖ ≤ C * |t-s|) :
    ‖actualSingularGreenCoeff K (r0 t) (F t) B -
        actualSingularGreenCoeff K (r0 s) (F t) B -
        actualSingularGreenCoeff K (r0 t) (F s) B +
        actualSingularGreenCoeff K (r0 s) (F s) B‖ ≤
      (C * |t-s|) * |r0 s - r0 t| := by
  rw [actual_origin_SingularGreen_moving_source_mixed_difference_exact
    K F r0 s t B htShort htLong hsShort hsLong]
  exact intervalIntegral.norm_integral_le_of_norm_le_const hLip

/-- A specialization to ONE original quartic Hartree interaction,
ONE real Cramer-selected speed and the TRUE moving slow-inner matching
radius. No arbitrary inner or outer source is introduced. -/
theorem actual_Hartree_true_selected_moving_SingularGreen_mixed_difference
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s t B C : ℝ)
    (htShort : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
      volume
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s))
    (htLong : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
      volume (actualHartreeSlowInnerRadius (ell s) / a s) B)
    (hsShort : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s))
    (hsLong : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume (actualHartreeSlowInnerRadius (ell s) / a s) B)
    (hLip : ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
      ‖originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) x -
        originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) x‖ ≤
        C * |t-s|) :
    let F : ℝ → ℝ → ℂ :=
      fun τ => actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ
    let r0 : ℝ → ℝ :=
      fun τ => actualHartreeSlowInnerRadius (ell τ) / a τ
    ‖actualSingularGreenCoeff K (r0 t) (F t) B -
        actualSingularGreenCoeff K (r0 s) (F t) B -
        actualSingularGreenCoeff K (r0 t) (F s) B +
        actualSingularGreenCoeff K (r0 s) (F s) B‖ ≤
      (C * |t-s|) * |r0 s - r0 t| := by
  exact actual_origin_SingularGreen_moving_source_mixed_difference_Lipschitz
    K
    (fun τ => actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ)
    (fun τ => actualHartreeSlowInnerRadius (ell τ) / a τ)
    s t B C htShort htLong hsShort hsLong hLip


def actualOriginSingularGreenMovingSelectedCross
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s B t : ℝ) : ℂ :=
  actualSingularGreenCoeff K (r0 t) (F t) B -
    actualSingularGreenCoeff K (r0 s) (F t) B -
    actualSingularGreenCoeff K (r0 t) (F s) B +
    actualSingularGreenCoeff K (r0 s) (F s) B

/-- The mixed moving-source/endpoint term has zero time derivative.
The O(|dt|*|dr|) estimate is DERIVED from the original integral,
not inserted as an arbitrary vanishing-error hypothesis. -/
theorem actual_origin_SingularGreen_moving_selected_cross_hasDerivAt_zero
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s B C rdot : ℝ)
    (T : Set ℝ) (hT : T ∈ 𝓝 s)
    (hR : HasDerivAt r0 rdot s)
    (hInt : ∀ t ∈ T,
      IntervalIntegrable (originGreenSourceA K (F t))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceA K (F t))
        volume (r0 s) B ∧
      IntervalIntegrable (originGreenSourceA K (F s))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceA K (F s))
        volume (r0 s) B)
    (hLip : ∀ t ∈ T, ∀ x ∈ uIoc (r0 t) (r0 s),
      ‖originGreenSourceA K (F t) x -
        originGreenSourceA K (F s) x‖ ≤ C * |t-s|) :
    HasDerivAt (actualOriginSingularGreenMovingSelectedCross K F r0 s B) 0 s := by
  have hZero : actualOriginSingularGreenMovingSelectedCross K F r0 s B s = 0 := by
    unfold actualOriginSingularGreenMovingSelectedCross
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
    actual_origin_SingularGreen_moving_source_mixed_difference_Lipschitz
      K F r0 s t B C
      (hInt t ht).1 (hInt t ht).2.1
      (hInt t ht).2.2.1 (hInt t ht).2.2.2
      (hLip t ht)
  change ‖actualOriginSingularGreenMovingSelectedCross K F r0 s B t‖ ≤
    (C * |t-s|) * |r0 s - r0 t| at hBound
  by_cases hEq : t = s
  · subst t
    simp [hZero]
  · have hAbs : 0 < |t-s| := abs_pos.mpr (sub_ne_zero.mpr hEq)
    calc
      ‖t-s‖⁻¹ *
        ‖actualOriginSingularGreenMovingSelectedCross K F r0 s B t -
          actualOriginSingularGreenMovingSelectedCross K F r0 s B s -
          (t-s) • (0 : ℂ)‖ =
        |t-s|⁻¹ * ‖actualOriginSingularGreenMovingSelectedCross K F r0 s B t‖ := by
          simp only [hZero, sub_zero, smul_zero, Real.norm_eq_abs]
      _ ≤ |t-s|⁻¹ * ((C * |t-s|) * |r0 s - r0 t|) :=
        mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr (abs_nonneg _))
      _ = C * |r0 s - r0 t| := by
        field_simp [hAbs.ne']

/-- Source-time and interface-time original Green partial derivatives
compose to the full joint derivative. Only the explicit moving-interval
source-density time Lipschitz hypothesis is additional. -/
theorem actual_origin_SingularGreen_moving_selected_joint_hasDerivAt
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ)
    (s B C rdot : ℝ) (T : Set ℝ) (hT : T ∈ 𝓝 s)
    (hR : HasDerivAt r0 rdot s)
    (hInt : ∀ t ∈ T,
      IntervalIntegrable (originGreenSourceA K (F t))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceA K (F t))
        volume (r0 s) B ∧
      IntervalIntegrable (originGreenSourceA K (F s))
        volume (r0 t) (r0 s) ∧
      IntervalIntegrable (originGreenSourceA K (F s))
        volume (r0 s) B)
    (hLip : ∀ t ∈ T, ∀ x ∈ uIoc (r0 t) (r0 s),
      ‖originGreenSourceA K (F t) x -
        originGreenSourceA K (F s) x‖ ≤ C * |t-s|)
    (dSource dEnd : ℂ)
    (hSource : HasDerivAt
      (fun t => actualSingularGreenCoeff K (r0 s) (F t) B) dSource s)
    (hEndpoint : HasDerivAt
      (fun t => actualSingularGreenCoeff K (r0 t) (F s) B) dEnd s) :
    HasDerivAt
      (fun t => actualSingularGreenCoeff K (r0 t) (F t) B)
      (dSource + dEnd) s := by
  have hCross :=
    actual_origin_SingularGreen_moving_selected_cross_hasDerivAt_zero
      K F r0 s B C rdot T hT hR hInt hLip
  have hTotal :=
    ((hSource.add hEndpoint).sub
      (hasDerivAt_const s (actualSingularGreenCoeff K (r0 s) (F s) B))).add hCross
  convert hTotal using 1
  · funext t
    simp only [Pi.add_apply, Pi.sub_apply,
      actualOriginSingularGreenMovingSelectedCross]
    abel
  · simp


end HBL.TypeIIDynamicSelection
