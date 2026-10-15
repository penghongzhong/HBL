import HBL.AbsoluteBubbleModulation

/-!
Two exact identities needed to compare the arbitrary-bubble Hilbert chart
with the manuscript's original threshold equations.

1. Fixed phase rotation followed by a relative phase delta is exactly
   the absolute phase gamma0+delta.
2. If a compact test is supported before S and the relative logarithmic
   scale b lies in [-1,1], then the fixed cutoff exp(-a0) R0 captures the
   entire transported support whenever exp(1) S <= R0.

No implicit-function or analytic approximation is used here.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff Interval

namespace HBL.Modulation

section PhaseComposition

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed phase rotation by gamma0 and a relative phase delta combine
exactly to the absolute phase gamma0+delta in the tested observable. -/
theorem scalePhaseObservable_phaseRotation_add
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ))
    (u : V × V) (a gamma₀ delta : ℝ) :
    scalePhaseObservable Splus Sminus
        (phaseRotationCLE (E := V) gamma₀ u, (a, delta)) =
      scalePhaseObservable Splus Sminus
        (u, (a, gamma₀ + delta)) := by
  rw [phaseRotationCLE_apply, phaseRotationCLM_apply]
  unfold scalePhaseObservable
  apply Prod.ext
  · simp only [map_add, map_smul, smul_eq_mul]
    rw [Real.cos_add, Real.sin_add]
    ring
  · simp only [map_add, map_smul, smul_eq_mul]
    rw [Real.sin_add, Real.cos_add]
    ring

/-- The same identity inside the normalized residual, whose base
subtraction is unchanged by the current state. -/
theorem scalePhaseResidual_phaseRotation_add
    (Splus Sminus : ℝ → (V →L[ℝ] ℝ))
    (w : V) (u : V × V) (a gamma₀ delta : ℝ) :
    scalePhaseResidual Splus Sminus w
        (phaseRotationCLE (E := V) gamma₀ u, (a, delta)) =
      scalePhaseObservable Splus Sminus
        (u, (a, gamma₀ + delta)) -
      scalePhaseObservable Splus Sminus
        ((w, (0 : V)), (0 : Param)) := by
  unfold scalePhaseResidual
  rw [scalePhaseObservable_phaseRotation_add
    Splus Sminus u a gamma₀ delta]

end PhaseComposition

/-- On the relative logarithmic-scale window [-1,1], the fixed cutoff
exp(-a0) R0 captures the support transported by the absolute scale a0+b. -/
theorem transportedRadialTestIntegral_centered_fixed_eq_dynamic_of_support
    (S R₀ : ℝ) (hS : 0 ≤ S)
    (hcover : Real.exp 1 * S ≤ R₀)
    (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : Continuous f)
    (hsupp : ∀ y : ℝ, S ≤ y → zeta y = 0)
    (a₀ b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    transportedRadialTestIntegral
        (Real.exp (-a₀) * R₀) zeta f (a₀ + b) =
      transportedRadialTestIntegral
        (Real.exp (-(a₀ + b)) * S) zeta f (a₀ + b) := by
  let D : ℝ := Real.exp (-(a₀ + b)) * S
  let Rout : ℝ := Real.exp (-a₀) * R₀
  let F : ℝ → ℝ :=
    fun r => transportedRadialTest zeta (a₀ + b) r * f r
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (Real.exp_pos _).le hS
  have hRout0 : 0 ≤ Rout := by
    dsimp [Rout]
    exact mul_nonneg (Real.exp_pos _).le
      (hcover.trans' (mul_nonneg (Real.exp_pos 1).le hS))
  have hexpb : Real.exp (-b) ≤ Real.exp 1 := by
    exact Real.exp_le_exp.mpr (by linarith [hb.1])
  have hinner : Real.exp (-b) * S ≤ R₀ := by
    exact (mul_le_mul_of_nonneg_right hexpb hS).trans hcover
  have hDfactor :
      D = Real.exp (-a₀) * (Real.exp (-b) * S) := by
    dsimp [D]
    have hsum : -(a₀ + b) = -a₀ + (-b) := by ring
    rw [hsum, Real.exp_add]
    ring
  have hDle : D ≤ Rout := by
    rw [hDfactor]
    dsimp [Rout]
    exact mul_le_mul_of_nonneg_left hinner (Real.exp_pos (-a₀)).le
  have hF : Continuous F := by
    dsimp [F, transportedRadialTest]
    fun_prop
  have h0D : IntervalIntegrable F volume 0 D :=
    hF.intervalIntegrable (μ := volume) (a := 0) (b := D)
  have hDR : IntervalIntegrable F volume D Rout :=
    hF.intervalIntegrable (μ := volume) (a := D) (b := Rout)
  have hscaleD : Real.exp (a₀ + b) * D = S := by
    dsimp [D]
    calc
      Real.exp (a₀ + b) *
          (Real.exp (-(a₀ + b)) * S) =
        (Real.exp (a₀ + b) *
          Real.exp (-(a₀ + b))) * S := by ring
      _ = S := by
        rw [← Real.exp_add]
        simp
  have htail : (∫ r in D..Rout, F r) = 0 := by
    calc
      (∫ r in D..Rout, F r) =
          ∫ r in D..Rout, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hDle] at hr
        have hyr : S ≤ Real.exp (a₀ + b) * r := by
          calc
            S = Real.exp (a₀ + b) * D := hscaleD.symm
            _ ≤ Real.exp (a₀ + b) * r :=
              mul_le_mul_of_nonneg_left hr.1
                (Real.exp_pos (a₀ + b)).le
        have hz0 := hsupp (Real.exp (a₀ + b) * r) hyr
        dsimp [F, transportedRadialTest]
        rw [hz0]
        ring
      _ = 0 := by simp
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h0D hDR
  rw [htail, add_zero] at hadd
  change (∫ r in (0 : ℝ)..Rout, F r) =
    ∫ r in (0 : ℝ)..D, F r
  exact hadd.symm

/-- Arbitrary-base version of the exact manuscript testing identity:
the fixed Hilbert cutoff equals the original compact threshold pairing
at the absolute logarithmic scale a0+b. -/
theorem transportedRadialTestIntegral_centered_eq_compactThresholdPairing
    (S R₀ : ℝ) (hS : 0 ≤ S)
    (hcover : Real.exp 1 * S ≤ R₀)
    (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : Continuous f)
    (hsupp : ∀ y : ℝ, S ≤ y → zeta y = 0)
    (a₀ b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    transportedRadialTestIntegral
        (Real.exp (-a₀) * R₀) zeta f (a₀ + b) =
      compactThresholdPairing S zeta
        (scalePullback f (a₀ + b)) := by
  rw [transportedRadialTestIntegral_centered_fixed_eq_dynamic_of_support
    S R₀ hS hcover zeta f hzeta hf hsupp a₀ b hb]
  rw [transportedRadialTestIntegral_dynamic_eq_scalePullback
    S zeta f (a₀ + b)]
  unfold compactThresholdPairing
  rw [intervalIntegral.integral_of_le hS]

end HBL.Modulation
