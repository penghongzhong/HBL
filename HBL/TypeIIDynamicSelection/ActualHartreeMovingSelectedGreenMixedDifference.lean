import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeSlowInnerMovingGreenEndpoint
import HBL.TypeIIDynamicSelection.ActualOriginGreenSourceTimeDerivative
import Mathlib.Tactic

/-!
# Genuine Hartree source and moving Green endpoint: exact mixed-difference identity

The true selected quartic nonlocal physical Hartree source is
F(s,r) = -a(s)^2 S_H(ell(s),c(s),z(s);a(s)r)
         - p_b(s) S_b(s,r) - p_w(s) S_w(s,r),
with p(s) the previously proved unique REAL Cramer-selected pair.

For the actual slow-inner radius R(s)=ell(s)^(-1/16)/a(s), the
right-hand-side original lower Green coefficient is G(R(s),F(s)).
Its failure to split naively into independent source and endpoint
increments is exactly a mixed interval integral, not an unknown
homogeneous constant or an abstract remainder packet.

This file proves the exact identity and a sharp moving-interval
Lipschitz estimate. An O(|t-s|) source-density difference gives
an O(|t-s|*|R(t)-R(s)|) mixed contribution with no scale loss.
It does not presuppose the Type-II rate, physical source time
regularity, moving basis estimates, or the full O(s^(-9/4)) PDE residual.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Exact two-parameter Green mixed difference. All four integrability
requirements refer to the ORIGINAL Wronskian densities, not an
independent synthetic forcing. They can be obtained from original
Hartree source continuity and the normalized Kummer annular basis. -/
theorem actual_origin_Green_moving_source_mixed_difference_exact
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s t B : ℝ)
    (htShort : IntervalIntegrable (originGreenSourceB K (F t))
      volume (r0 t) (r0 s))
    (htLong : IntervalIntegrable (originGreenSourceB K (F t))
      volume (r0 s) B)
    (hsShort : IntervalIntegrable (originGreenSourceB K (F s))
      volume (r0 t) (r0 s))
    (hsLong : IntervalIntegrable (originGreenSourceB K (F s))
      volume (r0 s) B) :
    originGreenCoeffB K (r0 t) (F t) B -
      originGreenCoeffB K (r0 s) (F t) B -
      originGreenCoeffB K (r0 t) (F s) B +
      originGreenCoeffB K (r0 s) (F s) B =
      ∫ x in (r0 t)..(r0 s),
        (originGreenSourceB K (F t) x -
          originGreenSourceB K (F s) x) := by
  have htSplit :
      originGreenCoeffB K (r0 t) (F t) B =
        (∫ x in (r0 t)..(r0 s), originGreenSourceB K (F t) x) +
          originGreenCoeffB K (r0 s) (F t) B := by
    exact (intervalIntegral.integral_add_adjacent_intervals htShort htLong).symm
  have hsSplit :
      originGreenCoeffB K (r0 t) (F s) B =
        (∫ x in (r0 t)..(r0 s), originGreenSourceB K (F s) x) +
          originGreenCoeffB K (r0 s) (F s) B := by
    exact (intervalIntegral.integral_add_adjacent_intervals hsShort hsLong).symm
  rw [htSplit, hsSplit, intervalIntegral.integral_sub htShort hsShort]
  abel

/-- Exact upper bound for the cross effect of changing the physical
Hartree source while the real lower interface moves.  No order
assumption on r0(t) versus r0(s) is needed. -/
theorem actual_origin_Green_moving_source_mixed_difference_Lipschitz
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (F : ℝ → ℝ → ℂ) (r0 : ℝ → ℝ) (s t B C : ℝ)
    (htShort : IntervalIntegrable (originGreenSourceB K (F t))
      volume (r0 t) (r0 s))
    (htLong : IntervalIntegrable (originGreenSourceB K (F t))
      volume (r0 s) B)
    (hsShort : IntervalIntegrable (originGreenSourceB K (F s))
      volume (r0 t) (r0 s))
    (hsLong : IntervalIntegrable (originGreenSourceB K (F s))
      volume (r0 s) B)
    (hLip : ∀ x ∈ uIoc (r0 t) (r0 s),
      ‖originGreenSourceB K (F t) x -
        originGreenSourceB K (F s) x‖ ≤ C * |t-s|) :
    ‖originGreenCoeffB K (r0 t) (F t) B -
        originGreenCoeffB K (r0 s) (F t) B -
        originGreenCoeffB K (r0 t) (F s) B +
        originGreenCoeffB K (r0 s) (F s) B‖ ≤
      (C * |t-s|) * |r0 s - r0 t| := by
  rw [actual_origin_Green_moving_source_mixed_difference_exact
    K F r0 s t B htShort htLong hsShort hsLong]
  exact intervalIntegral.norm_integral_le_of_norm_le_const hLip

/-- A specialization to ONE original quartic Hartree interaction,
ONE real Cramer-selected speed and the TRUE moving slow-inner matching
radius. No arbitrary inner or outer source is introduced. -/
theorem actual_Hartree_true_selected_moving_Green_mixed_difference
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s t B C : ℝ)
    (htShort : IntervalIntegrable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
      volume
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s))
    (htLong : IntervalIntegrable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
      volume (actualHartreeSlowInnerRadius (ell s) / a s) B)
    (hsShort : IntervalIntegrable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s))
    (hsLong : IntervalIntegrable
      (originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume (actualHartreeSlowInnerRadius (ell s) / a s) B)
    (hLip : ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
      ‖originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) x -
        originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) x‖ ≤
        C * |t-s|) :
    let F : ℝ → ℝ → ℂ :=
      fun τ => actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ
    let r0 : ℝ → ℝ :=
      fun τ => actualHartreeSlowInnerRadius (ell τ) / a τ
    ‖originGreenCoeffB K (r0 t) (F t) B -
        originGreenCoeffB K (r0 s) (F t) B -
        originGreenCoeffB K (r0 t) (F s) B +
        originGreenCoeffB K (r0 s) (F s) B‖ ≤
      (C * |t-s|) * |r0 s - r0 t| := by
  exact actual_origin_Green_moving_source_mixed_difference_Lipschitz
    K
    (fun τ => actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ)
    (fun τ => actualHartreeSlowInnerRadius (ell τ) / a τ)
    s t B C htShort htLong hsShort hsLong hLip

end HBL.TypeIIDynamicSelection
