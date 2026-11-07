import HBL.TypeIIDynamicSelection.ActualHartreeCramerSpeedDerivativeBound
import HBL.TypeIIDynamicSelection.ActualOriginGreenMovingEndpointDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreen
import Mathlib.Tactic

/-!
# Actual selected Cramer speed and moving-endpoint Green source derivative

At a fixed spatial Kummer basis, an affine three-component physical source
F0(r) - p1(s) S(r) - p2(s) P(r) is selected by the SAME two-channel Cramer
matrix. The time derivative of its regular Green integral is derived from
the actual Cramer speed derivatives and from the moving lower endpoint;
neither speed derivative nor Green-coefficient derivative is a premise.

This is a true selected-source derivative for the frozen spatial shapes.
The still-open derivative terms caused by time-dependent physical F0, S, P
and the full moving Kummer basis must be added in the full parametrix.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The one true adjusted complex source with both compatible real speed
coefficients. All three spatial profiles use the same Kummer coordinate. -/
def actualCramerSelectedFrozenOuterSource
    (F0 S P : ℝ → ℂ) (b w Z : ℝ → ℂ) (t r : ℝ) : ℂ :=
  let p := actualRealCramerCorrection (b t) (w t) (Z t)
  F0 r - (p.1 : ℂ) * S r - (p.2 : ℂ) * P r

/-- Full derivative of the selected regular Green source integral,
including the moving lower limit and both selected speed directions.
The real speeds are computed by the same exact Cramer compatibility
identity, and their derivatives are not separately assumed. -/
theorem actual_Cramer_selected_frozen_Green_time_derivative
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (hlohi : lo < hi)
    (F0 S P : ℝ → ℂ)
    (hF0 : Continuous F0) (hS : Continuous S) (hP : Continuous P)
    (r0 : ℝ → ℝ) (s r0dot a B : ℝ)
    (hr0 : r0 s ∈ Ioo lo hi)
    (hr0dot : HasDerivAt r0 r0dot s)
    (ha : 0 < a) (hB : 0 < B)
    (b w Z : ℝ → ℂ) (bdot wdot Zdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hbNorm : ‖b s‖ ≤ a * B ^ 2)
    (hwNorm : ‖w s‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤
      actualRealCramerDet (b s) (w s)) :
    ∃ p1dot p2dot : ℝ,
      let p1 : ℝ → ℝ :=
        fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).1
      let p2 : ℝ → ℝ :=
        fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).2
      HasDerivAt p1 p1dot s ∧
      HasDerivAt p2 p2dot s ∧
      |p1dot| + |p2dot| ≤
        1024 / (a * B ^ 2) *
          ‖Zdot + (p1 s : ℂ) * bdot + (p2 s : ℂ) * wdot‖ ∧
      HasDerivAt
        (fun t =>
          originGreenCoeffB K (r0 t)
            (actualCramerSelectedFrozenOuterSource F0 S P b w Z t) hi)
        (r0dot • (-originGreenSourceB K F0 (r0 s)) -
          ((p1dot : ℂ) * originGreenCoeffB K (r0 s) S hi +
            (p1 s : ℂ) *
              (r0dot • (-originGreenSourceB K S (r0 s)))) -
          ((p2dot : ℂ) * originGreenCoeffB K (r0 s) P hi +
            (p2 s : ℂ) *
              (r0dot • (-originGreenSourceB K P (r0 s))))) s := by
  obtain ⟨p1dot, p2dot, hp1, hp2, hSpeed⟩ :=
    actual_real_Cramer_selected_speed_derivative_bound
      a B s ha hB b w Z bdot wdot Zdot
      hb hw hZ hbNorm hwNorm hdet
  let p1 : ℝ → ℝ :=
    fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).1
  let p2 : ℝ → ℝ :=
    fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).2
  refine ⟨p1dot, p2dot, ?_, ?_, ?_, ?_⟩
  · simpa only [p1] using hp1
  · simpa only [p2] using hp2
  · simpa only [p1, p2] using hSpeed
  have h0 :=
    actual_origin_Green_coeffB_moving_lower_hasDerivAt
      K hK hlohi F0 hF0 r0 s r0dot hr0 hr0dot
  have h1 :=
    actual_origin_Green_coeffB_moving_lower_hasDerivAt
      K hK hlohi S hS r0 s r0dot hr0 hr0dot
  have h2 :=
    actual_origin_Green_coeffB_moving_lower_hasDerivAt
      K hK hlohi P hP r0 s r0dot hr0 hr0dot
  have hp1c :
      HasDerivAt (fun t => (p1 t : ℂ)) (p1dot : ℂ) s :=
    hp1.ofReal_comp
  have hp2c :
      HasDerivAt (fun t => (p2 t : ℂ)) (p2dot : ℂ) s :=
    hp2.ofReal_comp
  have hPoly :=
    (h0.sub (hp1c.mul h1)).sub (hp2c.mul h2)
  have heventual : ∀ᶠ t in 𝓝 s, r0 t ∈ Ioo lo hi :=
    hr0dot.continuousAt.eventually (Ioo_mem_nhds hr0.1 hr0.2)
  have hEq : ∀ᶠ t in 𝓝 s,
      originGreenCoeffB K (r0 t)
        (actualCramerSelectedFrozenOuterSource F0 S P b w Z t) hi =
      originGreenCoeffB K (r0 t) F0 hi -
        (p1 t : ℂ) * originGreenCoeffB K (r0 t) S hi -
        (p2 t : ℂ) * originGreenCoeffB K (r0 t) P hi := by
    filter_upwards [heventual] with t ht
    have hKt : OriginBasisOn K (r0 t) hi C := by
      intro u hu
      exact hK u ⟨(le_of_lt ht.1).trans hu.1, hu.2⟩
    have hIF0 : IntervalIntegrable F0 volume (r0 t) hi :=
      hF0.intervalIntegrable _ _
    have hIS : IntervalIntegrable S volume (r0 t) hi :=
      hS.intervalIntegrable _ _
    have hIP : IntervalIntegrable P volume (r0 t) hi :=
      hP.intervalIntegrable _ _
    let F1 : ℝ → ℂ := fun u => F0 u + (-(p1 t : ℂ)) * S u
    have hIF1 : IntervalIntegrable F1 volume (r0 t) hi :=
      hIF0.add (hIS.const_mul (-(p1 t : ℂ)))
    have hAdd1 :=
      actual_moment_locked_regular_source_coefficient_add_mul_on
        K hKt ht.2.le F0 S hIF0 hIS (-(p1 t : ℂ))
    have hAdd2 :=
      actual_moment_locked_regular_source_coefficient_add_mul_on
        K hKt ht.2.le F1 P hIF1 hIP (-(p2 t : ℂ))
    have hFrozenSource :
        actualCramerSelectedFrozenOuterSource F0 S P b w Z t =
          (fun u => F0 u + (-(p1 t : ℂ)) * S u +
            (-(p2 t : ℂ)) * P u) := by
      funext u
      dsimp [actualCramerSelectedFrozenOuterSource, p1, p2]
      ring
    rw [hFrozenSource]
    change originGreenCoeffB K (r0 t)
      (fun u => F0 u + (-(p1 t : ℂ)) * S u +
        (-(p2 t : ℂ)) * P u) hi = _
    rw [← show
        (fun u : ℝ => F0 u + (-(p1 t : ℂ)) * S u +
          (-(p2 t : ℂ)) * P u) =
          (fun u => F1 u + (-(p2 t : ℂ)) * P u) from rfl,
      hAdd2, hAdd1]
    ring
  exact hPoly.congr_of_eventuallyEq hEq

end HBL.TypeIIDynamicSelection
