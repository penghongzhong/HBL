import HBL.TransportedThresholdIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Compact-support removal of the moving endpoint.

If zeta vanishes for r >= S and |a| <= 1, then the transported kernel
vanishes for r >= exp(-a) S.  Thus any fixed radius R with exp(1) S <= R
contains the transported support for every a in [-1,1].

This upgrades the exact moving-endpoint change of variables to the fixed
finite-radius Hilbert model used by the modulation implicit-function proof.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff Interval

namespace HBL.Modulation

/-- On the local logarithmic-scale window [-1,1], a fixed outer radius
R >= exp(1) S captures the whole transported compact test. -/
theorem transportedRadialTestIntegral_fixed_eq_dynamic_of_support
    (S R : ℝ) (hS : 0 ≤ S)
    (hcover : Real.exp 1 * S ≤ R)
    (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : Continuous f)
    (hsupp : ∀ y : ℝ, S ≤ y → zeta y = 0)
    (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
    transportedRadialTestIntegral R zeta f a =
      transportedRadialTestIntegral (Real.exp (-a) * S) zeta f a := by
  let D : ℝ := Real.exp (-a) * S
  let F : ℝ → ℝ := fun r => transportedRadialTest zeta a r * f r
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (Real.exp_pos _).le hS
  have hDle : D ≤ R := by
    have he : Real.exp (-a) ≤ Real.exp 1 := by
      exact Real.exp_le_exp.mpr (by linarith [ha.1])
    have hmul : Real.exp (-a) * S ≤ Real.exp 1 * S :=
      mul_le_mul_of_nonneg_right he hS
    exact hmul.trans hcover
  have hF : Continuous F := by
    have hdz : Continuous (deriv zeta) := by
      exact continuous_zero
    dsimp [F, transportedRadialTest]
    fun_prop
  have h0D : IntervalIntegrable F volume 0 D :=
    hF.intervalIntegrable (μ := volume) (a := 0) (b := D)
  have hDR : IntervalIntegrable F volume D R :=
    hF.intervalIntegrable (μ := volume) (a := D) (b := R)
  have hscaleD : Real.exp a * D = S := by
    dsimp [D]
    calc
      Real.exp a * (Real.exp (-a) * S) =
          (Real.exp a * Real.exp (-a)) * S := by ring
      _ = S := by
        rw [← Real.exp_add]
        simp
  have htail : (∫ r in D..R, F r) = 0 := by
    calc
      (∫ r in D..R, F r) = ∫ r in D..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hDle] at hr
        have hyr : S ≤ Real.exp a * r := by
          calc
            S = Real.exp a * D := hscaleD.symm
            _ ≤ Real.exp a * r :=
              mul_le_mul_of_nonneg_left hr.1 (Real.exp_pos a).le
        have hz0 := hsupp (Real.exp a * r) hyr
        dsimp [F, transportedRadialTest]
        rw [hz0]
        ring
      _ = 0 := by simp
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h0D hDR
  rw [htail, add_zero] at hadd
  change (∫ r in (0 : ℝ)..R, F r) =
    ∫ r in (0 : ℝ)..D, F r
  exact hadd.symm

/-- Exact identification with the manuscript's compact threshold pairing:
for a locally transported compact test, the fixed-radius Hilbert functional
is exactly ell_zeta(T_a f). -/
theorem transportedRadialTestIntegral_eq_compactThresholdPairing_of_support
    (S R : ℝ) (hS : 0 ≤ S)
    (hcover : Real.exp 1 * S ≤ R)
    (zeta f : ℝ → ℝ)
    (hzeta : Continuous zeta) (hf : Continuous f)
    (hsupp : ∀ y : ℝ, S ≤ y → zeta y = 0)
    (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
    transportedRadialTestIntegral R zeta f a =
      compactThresholdPairing S zeta (scalePullback f a) := by
  rw [transportedRadialTestIntegral_fixed_eq_dynamic_of_support
    S R hS hcover zeta f hzeta hf hsupp a ha]
  rw [transportedRadialTestIntegral_dynamic_eq_scalePullback S zeta f a]
  unfold compactThresholdPairing
  rw [intervalIntegral.integral_of_le hS]

end HBL.Modulation
