import HBL.TypeIIDynamicSelection.MonopoleRateLimit

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole

/-- A genuine PHYSICAL first-monopole Hartree threshold source bound.
The radial Hartree nonlinearity and its moving cutoff enter through the
already proved exact effective residual, and the compact test is the
actual normalized plus-channel source. The velocity and modulation paths
are constrained only by their primitive decay assumptions.

This is not the full nonlinear residual of a constructed Type II orbit. -/
theorem actual_firstMonopole_core_projection_quantitative
    {c b omega : ℝ → ℝ} {s0 beta A : ℝ}
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ)) :
    ∃ C D : ℝ, 0 < D ∧
      ∀ s : ℝ, s0 < s →
        ‖monopoleComplexCoreProjection normalizedZetaPlus c b omega s‖ ≤
          C * (monopoleStaticRadialBoundConstant * (c s) ^ 2 +
            monopoleRadialBoundConstant * |deriv c s| +
            D * |b s * c s| +
            monopoleRadialBoundConstant * |omega s * c s|) := by
  obtain ⟨D, hDpos, hDbound⟩ := monopoleComplexEffectiveIncrement_core_bound
  have htest : Continuous (fun r : ℝ => r * normalizedZetaPlus r) :=
    continuous_id.mul normalizedZetaPlus_contDiff_infty.continuous
  obtain ⟨Z,hZ⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn htest.continuousOn
  let m : ℝ := (volume.restrict (Ioo (0 : ℝ) 1)).real univ
  refine ⟨|Z| * m, D, hDpos, ?_⟩
  intro s hs
  let E : ℝ :=
    monopoleStaticRadialBoundConstant * (c s) ^ 2 +
    monopoleRadialBoundConstant * |deriv c s| +
    D * |b s * c s| +
    monopoleRadialBoundConstant * |omega s * c s|
  have hcore (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      |c s| * r / 4 ≤ 1 / 2 := by
    have hcr : |c s| * r ≤ 1 :=
      (mul_le_mul (hsmall s hs) hr.2.le hr.1.le zero_le_one).trans_eq (one_mul 1)
    linarith
  have hpoint (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      ‖(r * normalizedZetaPlus r : ℝ) *
        monopoleComplexEffectiveIncrement c (b s) (omega s) s r‖ ≤
        |Z| * E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hrZ : |r * normalizedZetaPlus r| ≤ |Z| :=
      (by simpa only [Real.norm_eq_abs] using hZ r ⟨hr.1.le, hr.2.le⟩).trans
        (le_abs_self Z)
    exact mul_le_mul hrZ
      (hDbound c (deriv c s) s r (b s) (omega s) (hc s).hasDerivAt
        (hsmall s hs) hr.1 (hcore r hr))
      (norm_nonneg _) (abs_nonneg _)
  have htotal :
      ‖monopoleComplexCoreProjection normalizedZetaPlus c b omega s‖ ≤
        (|Z| * E) * m := by
    unfold monopoleComplexCoreProjection
    exact norm_integral_le_of_norm_le_const (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hpoint r hr)
  calc
    ‖monopoleComplexCoreProjection normalizedZetaPlus c b omega s‖ ≤
        (|Z| * E) * m := htotal
    _ = (|Z| * m) * E := by ring

end HBL.TypeIIDynamicSelection
