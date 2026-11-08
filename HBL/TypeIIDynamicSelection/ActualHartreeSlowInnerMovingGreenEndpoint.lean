import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import HBL.TypeIIDynamicSelection.ActualOriginGreenMovingEndpointDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Actual moving Hartree inner matching radius and original Green endpoint

The genuine source-localization matching radius is not a chosen scalar
packet: L(ell) = ell^(-1/16), and its normalized Kummer interface is
r0(s)=L(ell(s))/a(s). Both derivatives follow from the input physical
parameter path, without prescribing any Type-II blowup law.

The original Green moving-lower-endpoint theorem is specialized to the
SAME actual Cramer-selected original Hartree forcing evaluated at the
physical time slice s, not an independently invented source. Its
continuity is a visible hypothesis, not inferred from measurability.

This settles the geometric endpoint-transport derivative at a frozen
source and Kummer basis. The varying-source integral derivative, full
basis derivative, uniform PDE remainder and matching with the actual
time-evolving four-piece orbit are separate obligations.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_slow_inner_radius_time_derivative
    (ell : ℝ → ℝ) (s ellDot : ℝ)
    (hEll : HasDerivAt ell ellDot s) (hPos : 0 < ell s) :
    HasDerivAt (fun t => actualHartreeSlowInnerRadius (ell t))
      ((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) * ellDot) s := by
  have hPow :=
    (Real.hasDerivAt_rpow_const
      (p := -(1 / 16 : ℝ)) (Or.inl hPos.ne')).comp s hEll
  simpa only [actualHartreeSlowInnerRadius, Function.comp_def] using hPow

theorem actual_Hartree_slow_inner_Kummer_endpoint_time_derivative
    (ell a : ℝ → ℝ) (s ellDot aDot : ℝ)
    (hEll : HasDerivAt ell ellDot s)
    (hA : HasDerivAt a aDot s)
    (hPos : 0 < ell s) (ha : 0 < a s) :
    HasDerivAt
      (fun t => actualHartreeSlowInnerRadius (ell t) / a t)
      (((-(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
           ellDot * a s -
          actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2) s := by
  have hL :=
    actual_Hartree_slow_inner_radius_time_derivative ell s ellDot hEll hPos
  exact hL.div hA ha.ne'

/-- The actual selected original quartic Hartree source is fixed at this
physical time when differentiating its true moving Green lower endpoint.
No independent lower-endpoint velocity or selected speed is assumed. -/
theorem actual_Hartree_true_source_slow_inner_moving_Green_endpoint
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (hlohi : lo < hi)
    (ell a c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ)
    (s ellDot aDot : ℝ)
    (hEll : HasDerivAt ell ellDot s)
    (hA : HasDerivAt a aDot s)
    (hPos : 0 < ell s) (ha : 0 < a s)
    (hr0 : actualHartreeSlowInnerRadius (ell s) / a s ∈ Ioo lo hi)
    (hF : Continuous
      (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s)) :
    HasDerivAt
      (fun t => originGreenCoeffB K
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) hi)
      (((( -(1 / 16 : ℝ)) * (ell s) ^ (-(1 / 16 : ℝ) - 1) *
           ellDot * a s -
          actualHartreeSlowInnerRadius (ell s) * aDot) / (a s) ^ 2) •
        (-originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s)
          (actualHartreeSlowInnerRadius (ell s) / a s))) s := by
  have hR :=
    actual_Hartree_slow_inner_Kummer_endpoint_time_derivative
      ell a s ellDot aDot hEll hA hPos ha
  exact actual_origin_Green_coeffB_moving_lower_hasDerivAt
    K hK hlohi
      (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s)
      hF (fun t => actualHartreeSlowInnerRadius (ell t) / a t)
      s _ hr0 hR

end HBL.TypeIIDynamicSelection
