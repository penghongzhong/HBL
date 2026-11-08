import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSpeedSelection
import HBL.TypeIIDynamicSelection.ActualHartreeCramerSpeedDerivativeBound
import Mathlib.Tactic

/-!
# One moving, original nonlocal Hartree source with both selected real speeds

Unlike frozen-shape Green derivative statements, this statement retains all
three time-dependent spatial sources: the *original* quartic Hartree Riesz
forcing and the genuine two modulation directions. The selected speed is the
actual Cramer function of the evolving compatibility columns and obstruction,
not an independently specified differentiable function.

The time derivatives of the three *original* physical source functions remain
explicit analytic inputs: they cannot be deduced from mere measurability of
the radiation. This lemma proves the complete algebraic time differentiation,
including the previously omitted moving physical sources and both selected
speed derivatives, and derives the latter from the Cramer determinant.

This fixed-radius derivative is not yet the moving Kummer basis, the complete
moving-interface PDE residual, or the rate-9/4 weighted bound.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The literal full physical Hartree source, adjusted by the unique
real Cramer pair of the evolving compatibility data. -/
def actualHartreeTrueMovingAdjustedSource
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (t r : ℝ) : ℂ :=
  let p := actualRealCramerCorrection (b t) (w t) (Z t);
  -actualHartreeLaplacianScaledKummerSource
      (a t) (ell t) (c t) (z t) r -
    (p.1 : ℂ) * actualMomentLockedScaledScaleSource (a t) (c t) r -
    (p.2 : ℂ) * actualMomentLockedScaledPhaseSource (a t) (c t) r

/-- Full time derivative of the genuine moving Hartree source after Cramer
selection. In particular, neither real speed derivative is assumed. -/
theorem actual_Hartree_true_moving_adjusted_source_derivative
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s r alpha B : ℝ)
    (halpha : 0 < alpha) (hB : 0 < B)
    (bdot wdot Zdot Fdot Sdot Pdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hbNorm : ‖b s‖ ≤ alpha * B ^ 2)
    (hwNorm : ‖w s‖ ≤ alpha * B ^ 2)
    (hdet : alpha ^ 2 * B ^ 4 / 256 ≤
      actualRealCramerDet (b s) (w s))
    (hF : HasDerivAt
      (fun t => -actualHartreeLaplacianScaledKummerSource
        (a t) (ell t) (c t) (z t) r) Fdot s)
    (hS : HasDerivAt
      (fun t => actualMomentLockedScaledScaleSource (a t) (c t) r) Sdot s)
    (hP : HasDerivAt
      (fun t => actualMomentLockedScaledPhaseSource (a t) (c t) r) Pdot s) :
    ∃ pbDot pwDot : ℝ,
      let pb : ℝ → ℝ := fun t =>
        (actualRealCramerCorrection (b t) (w t) (Z t)).1
      let pw : ℝ → ℝ := fun t =>
        (actualRealCramerCorrection (b t) (w t) (Z t)).2
      HasDerivAt pb pbDot s ∧
      HasDerivAt pw pwDot s ∧
      |pbDot| + |pwDot| ≤
        1024 / (alpha * B ^ 2) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ ∧
      HasDerivAt
        (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t r)
        (Fdot -
          ((pbDot : ℂ) *
              actualMomentLockedScaledScaleSource (a s) (c s) r +
            (pb s : ℂ) * Sdot) -
          ((pwDot : ℂ) *
              actualMomentLockedScaledPhaseSource (a s) (c s) r +
            (pw s : ℂ) * Pdot)) s := by
  obtain ⟨pbDot, pwDot, hpb, hpw, hSpeed⟩ :=
    actual_real_Cramer_selected_speed_derivative_bound
      alpha B s halpha hB b w Z bdot wdot Zdot
      hb hw hZ hbNorm hwNorm hdet
  let pb : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).1
  let pw : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).2
  have hpbReal : HasDerivAt pb pbDot s := by
    simpa only [pb] using hpb
  have hpwReal : HasDerivAt pw pwDot s := by
    simpa only [pw] using hpw
  have hpbC : HasDerivAt (fun t => (pb t : ℂ)) (pbDot : ℂ) s :=
    hpbReal.ofReal_comp
  have hpwC : HasDerivAt (fun t => (pw t : ℂ)) (pwDot : ℂ) s :=
    hpwReal.ofReal_comp
  have hTotal := (hF.sub (hpbC.mul hS)).sub (hpwC.mul hP)
  refine ⟨pbDot, pwDot, hpbReal, hpwReal, ?_, ?_⟩
  · simpa only [pb, pw] using hSpeed
  · simpa only [actualHartreeTrueMovingAdjustedSource, pb, pw,
      Pi.sub_apply, Pi.mul_apply] using hTotal

end HBL.TypeIIDynamicSelection
