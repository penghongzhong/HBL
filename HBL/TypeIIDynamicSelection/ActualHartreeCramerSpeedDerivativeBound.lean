import HBL.TypeIIDynamicSelection.ActualHartreeCramerSelectorDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeDifferentiatedCompatibility
import Mathlib.Tactic

/-!
# Quantitative derivative bound for the explicit selected Cramer speeds

The accepted selector is a concrete rational function of the two compatibility
columns and the obstruction.  Its exact differentiability is already strict.
Because the determinant is positive at the selected point, continuity keeps it
nonzero on a neighborhood, so the SAME Cramer pair satisfies the compatibility
identity locally.  Differentiating that identity and reusing the SAME strict
two-column inverse gives the speed-derivative estimate.

No new determinant argument and no quotient-norm estimate are introduced.
-/

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_real_Cramer_selected_speed_derivative_bound
    (a B s : ℝ) (ha : 0 < a) (hB : 0 < B)
    (b w Z : ℝ → ℂ) (bdot wdot Zdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hbNorm : ‖b s‖ ≤ a * B ^ 2)
    (hwNorm : ‖w s‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤
      actualRealCramerDet (b s) (w s)) :
    let p1 : ℝ → ℝ :=
      fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).1
    let p2 : ℝ → ℝ :=
      fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).2
    ∃ p1dot p2dot : ℝ,
      HasDerivAt p1 p1dot s ∧
      HasDerivAt p2 p2dot s ∧
      |p1dot| + |p2dot| ≤
        1024 / (a * B ^ 2) *
          ‖Zdot + (p1 s : ℂ) * bdot + (p2 s : ℂ) * wdot‖ := by
  dsimp only
  let p1 : ℝ → ℝ :=
    fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).1
  let p2 : ℝ → ℝ :=
    fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).2
  have hbase : 0 < a ^ 2 * B ^ 4 / 256 := by positivity
  have hdetPos : 0 < actualRealCramerDet (b s) (w s) :=
    hbase.trans_le hdet
  have hdetNe : actualRealCramerDet (b s) (w s) ≠ 0 :=
    hdetPos.ne'
  have hData :=
    actual_real_Cramer_data_derivatives
      b w Z s bdot wdot Zdot hb hw hZ
  have hCramer :=
    actual_real_Cramer_correction_component_derivatives
      b w Z s bdot wdot Zdot hb hw hZ hdetNe
  have hp1diff : DifferentiableAt ℝ p1 s := by
    dsimp [p1]
    exact hCramer.1.differentiableAt
  have hp2diff : DifferentiableAt ℝ p2 s := by
    dsimp [p2]
    exact hCramer.2.differentiableAt
  let p1dot : ℝ := deriv p1 s
  let p2dot : ℝ := deriv p2 s
  have hp1 : HasDerivAt p1 p1dot s := by
    dsimp [p1dot]
    exact hp1diff.hasDerivAt
  have hp2 : HasDerivAt p2 p2dot s := by
    dsimp [p2dot]
    exact hp2diff.hasDerivAt
  have hdetNear :
      ∀ᶠ t in 𝓝 s, actualRealCramerDet (b t) (w t) ≠ 0 :=
    hData.1.continuousAt.eventually_ne hdetNe
  have hlocal :
      ∀ᶠ t in 𝓝 s,
        Z t + (p1 t : ℂ) * b t + (p2 t : ℂ) * w t = 0 := by
    filter_upwards [hdetNear] with t ht
    have hc := actual_real_Cramer_correction_cancel
      (b t) (w t) (Z t) ht
    simpa only [p1, p2] using hc
  have hSpeed :=
    actual_complex_columns_differentiated_cancellation_bound_clean
      a B s ha hB b w Z p1 p2 bdot wdot Zdot p1dot p2dot
      hb hw hZ hp1 hp2 hlocal hbNorm hwNorm hdet
  exact ⟨p1dot,p2dot,hp1,hp2,hSpeed⟩

end HBL.TypeIIDynamicSelection
