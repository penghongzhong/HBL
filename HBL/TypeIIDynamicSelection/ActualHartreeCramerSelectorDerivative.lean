import HBL.TypeIIDynamicSelection.ActualHartreeCramerSelector
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Exact time derivative of the explicit real Cramer selector

The compatibility correction is now a concrete rational function of two
complex columns and one complex obstruction.  This file differentiates that
rational function along arbitrary real curves.  No bound is inserted here;
the subsequent quantitative step can combine this identity with the already
strict determinant lower bound and column/obstruction derivative estimates.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

def actualRealCramerDet (b w : ℂ) : ℝ :=
  b.re * w.im - w.re * b.im

def actualRealCramerNum1 (w Z : ℂ) : ℝ :=
  w.re * Z.im - w.im * Z.re

def actualRealCramerNum2 (b Z : ℂ) : ℝ :=
  b.im * Z.re - b.re * Z.im

def actualRealCramerDetDot (b w bdot wdot : ℂ) : ℝ :=
  bdot.re * w.im + b.re * wdot.im -
    (wdot.re * b.im + w.re * bdot.im)

def actualRealCramerNum1Dot (w Z wdot Zdot : ℂ) : ℝ :=
  wdot.re * Z.im + w.re * Zdot.im -
    (wdot.im * Z.re + w.im * Zdot.re)

def actualRealCramerNum2Dot (b Z bdot Zdot : ℂ) : ℝ :=
  bdot.im * Z.re + b.im * Zdot.re -
    (bdot.re * Z.im + b.re * Zdot.im)

private theorem complex_curve_re_hasDerivAt
    (f : ℝ → ℂ) (s : ℝ) (fdot : ℂ)
    (hf : HasDerivAt f fdot s) :
    HasDerivAt (fun t => (f t).re) fdot.re s := by
  have hc : HasDerivAt (fun _ : ℝ => Complex.reCLM)
      (0 : ℂ →L[ℝ] ℝ) s := hasDerivAt_const s Complex.reCLM
  have h := hc.clm_apply hf
  simpa only [zero_apply, zero_add, Complex.reCLM_apply] using h

private theorem complex_curve_im_hasDerivAt
    (f : ℝ → ℂ) (s : ℝ) (fdot : ℂ)
    (hf : HasDerivAt f fdot s) :
    HasDerivAt (fun t => (f t).im) fdot.im s := by
  have hc : HasDerivAt (fun _ : ℝ => Complex.imCLM)
      (0 : ℂ →L[ℝ] ℝ) s := hasDerivAt_const s Complex.imCLM
  have h := hc.clm_apply hf
  simpa only [zero_apply, zero_add, Complex.imCLM_apply] using h

theorem actual_real_Cramer_data_derivatives
    (b w Z : ℝ → ℂ) (s : ℝ)
    (bdot wdot Zdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s) :
    HasDerivAt
      (fun t => actualRealCramerDet (b t) (w t))
      (actualRealCramerDetDot (b s) (w s) bdot wdot) s ∧
    HasDerivAt
      (fun t => actualRealCramerNum1 (w t) (Z t))
      (actualRealCramerNum1Dot (w s) (Z s) wdot Zdot) s ∧
    HasDerivAt
      (fun t => actualRealCramerNum2 (b t) (Z t))
      (actualRealCramerNum2Dot (b s) (Z s) bdot Zdot) s := by
  have hbr := complex_curve_re_hasDerivAt b s bdot hb
  have hbi := complex_curve_im_hasDerivAt b s bdot hb
  have hwr := complex_curve_re_hasDerivAt w s wdot hw
  have hwi := complex_curve_im_hasDerivAt w s wdot hw
  have hZr := complex_curve_re_hasDerivAt Z s Zdot hZ
  have hZi := complex_curve_im_hasDerivAt Z s Zdot hZ
  have hd0 := (hbr.mul hwi).sub (hwr.mul hbi)
  have hn10 := (hwr.mul hZi).sub (hwi.mul hZr)
  have hn20 := (hbi.mul hZr).sub (hbr.mul hZi)
  have hfd :
      ((fun t => (b t).re) * (fun t => (w t).im) -
        (fun t => (w t).re) * (fun t => (b t).im)) =
      (fun t => actualRealCramerDet (b t) (w t)) := by
    rfl
  have hfn1 :
      ((fun t => (w t).re) * (fun t => (Z t).im) -
        (fun t => (w t).im) * (fun t => (Z t).re)) =
      (fun t => actualRealCramerNum1 (w t) (Z t)) := by
    rfl
  have hfn2 :
      ((fun t => (b t).im) * (fun t => (Z t).re) -
        (fun t => (b t).re) * (fun t => (Z t).im)) =
      (fun t => actualRealCramerNum2 (b t) (Z t)) := by
    rfl
  rw [hfd] at hd0
  rw [hfn1] at hn10
  rw [hfn2] at hn20
  exact ⟨hd0, hn10, hn20⟩

/-- Exact quotient-rule derivatives of both selected real Cramer coordinates. -/
theorem actual_real_Cramer_correction_component_derivatives
    (b w Z : ℝ → ℂ) (s : ℝ)
    (bdot wdot Zdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hdet : actualRealCramerDet (b s) (w s) ≠ 0) :
    let d := actualRealCramerDet (b s) (w s)
    let ddot := actualRealCramerDetDot (b s) (w s) bdot wdot
    let n1 := actualRealCramerNum1 (w s) (Z s)
    let n1dot := actualRealCramerNum1Dot (w s) (Z s) wdot Zdot
    let n2 := actualRealCramerNum2 (b s) (Z s)
    let n2dot := actualRealCramerNum2Dot (b s) (Z s) bdot Zdot
    HasDerivAt
      (fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).1)
      ((n1dot * d - n1 * ddot) / d ^ 2) s ∧
    HasDerivAt
      (fun t => (actualRealCramerCorrection (b t) (w t) (Z t)).2)
      ((n2dot * d - n2 * ddot) / d ^ 2) s := by
  dsimp only
  obtain ⟨hd, hn1, hn2⟩ :=
    actual_real_Cramer_data_derivatives b w Z s bdot wdot Zdot hb hw hZ
  let d := actualRealCramerDet (b s) (w s)
  let ddot := actualRealCramerDetDot (b s) (w s) bdot wdot
  let n1 := actualRealCramerNum1 (w s) (Z s)
  let n1dot := actualRealCramerNum1Dot (w s) (Z s) wdot Zdot
  let n2 := actualRealCramerNum2 (b s) (Z s)
  let n2dot := actualRealCramerNum2Dot (b s) (Z s) bdot Zdot
  have hp10 := hn1.div hd hdet
  have hp20 := hn2.div hd hdet
  have hf1 :
      ((fun t => actualRealCramerNum1 (w t) (Z t)) /
        (fun t => actualRealCramerDet (b t) (w t))) =
      (fun t =>
        actualRealCramerNum1 (w t) (Z t) /
          actualRealCramerDet (b t) (w t)) := by
    rfl
  have hf2 :
      ((fun t => actualRealCramerNum2 (b t) (Z t)) /
        (fun t => actualRealCramerDet (b t) (w t))) =
      (fun t =>
        actualRealCramerNum2 (b t) (Z t) /
          actualRealCramerDet (b t) (w t)) := by
    rfl
  rw [hf1] at hp10
  rw [hf2] at hp20
  constructor
  · change HasDerivAt
      (fun t =>
        actualRealCramerNum1 (w t) (Z t) /
          actualRealCramerDet (b t) (w t))
      ((n1dot * d - n1 * ddot) / d ^ 2) s
    simpa only [d, ddot, n1, n1dot] using hp10
  · change HasDerivAt
      (fun t =>
        actualRealCramerNum2 (b t) (Z t) /
          actualRealCramerDet (b t) (w t))
      ((n2dot * d - n2 * ddot) / d ^ 2) s
    simpa only [d, ddot, n2, n2dot] using hp20

end HBL.TypeIIDynamicSelection
