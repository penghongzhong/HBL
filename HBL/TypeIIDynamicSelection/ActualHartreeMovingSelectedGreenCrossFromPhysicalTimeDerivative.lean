import HBL.TypeIIDynamicSelection.ActualHartreeMovingSelectedGreenMixedDifference
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Moving original Hartree Green cross term: physical time derivative to Lipschitz

The cross source/endpoint remainder is controlled by a time derivative
of the ORIGINAL selected Hartree Wronskian density, rather than by
assuming the density's time Lipschitz estimate as a separate input.

The time derivative is evaluated on the same Cramer-selected real
two-channel physical source, including the moving source directions.
Its uniform bound on the actual moving spatial interval is a visible
remaining PDE-orbit obligation. The lemma does not assert such a bound
without that input, and implies no positive residual time order.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- A real-time mean-value bridge: a bounded derivative of the genuine
selected nonlocal Hartree Green density produces the mixed
source/endpoint estimate with the exact product of the two increments.
This removes a free time-Lipschitz assumption from the matching argument. -/
theorem actual_Hartree_moving_selected_Green_cross_from_physical_time_derivative
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s t B C : ℝ) (hst : s ≤ t)
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
    (hTimeDeriv :
      ∀ x ∈ uIoc
          (actualHartreeSlowInnerRadius (ell t) / a t)
          (actualHartreeSlowInnerRadius (ell s) / a s),
        ∀ τ ∈ Icc s t, ∃ D : ℂ,
          HasDerivAt
            (fun v => originGreenSourceB K
              (actualHartreeTrueMovingAdjustedSource a ell c z b w Z v) x)
            D τ ∧ ‖D‖ ≤ C) :
    let F : ℝ → ℝ → ℂ :=
      fun τ => actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ
    let r0 : ℝ → ℝ :=
      fun τ => actualHartreeSlowInnerRadius (ell τ) / a τ
    ‖originGreenCoeffB K (r0 t) (F t) B -
        originGreenCoeffB K (r0 s) (F t) B -
        originGreenCoeffB K (r0 t) (F s) B +
        originGreenCoeffB K (r0 s) (F s) B‖ ≤
      (C * |t - s|) * |r0 s - r0 t| := by
  have hLip :
      ∀ x ∈ uIoc
          (actualHartreeSlowInnerRadius (ell t) / a t)
          (actualHartreeSlowInnerRadius (ell s) / a s),
        ‖originGreenSourceB K
            (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) x -
          originGreenSourceB K
            (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) x‖ ≤
          C * |t - s| := by
    intro x hx
    let f : ℝ → ℂ := fun v =>
      originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z v) x
    have hdifferentiable : ∀ v ∈ Icc s t, DifferentiableAt ℝ f v := by
      intro v hv
      obtain ⟨D, hD, _⟩ := hTimeDeriv x hx v hv
      exact hD.differentiableAt
    have hbound : ∀ v ∈ Icc s t, ‖deriv f v‖ ≤ C := by
      intro v hv
      obtain ⟨D, hD, hNorm⟩ := hTimeDeriv x hx v hv
      simpa only [hD.deriv] using hNorm
    have hMean := (convex_Icc s t).norm_image_sub_le_of_norm_deriv_le
      hdifferentiable hbound
      (show s ∈ Icc s t from ⟨le_refl s, hst⟩)
      (show t ∈ Icc s t from ⟨hst, le_refl t⟩)
    simpa only [f, Real.norm_eq_abs] using hMean
  exact actual_Hartree_true_selected_moving_Green_mixed_difference
    K a ell c z b w Z s t B C
    htShort htLong hsShort hsLong hLip

end HBL.TypeIIDynamicSelection
