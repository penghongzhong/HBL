import HBL.ScaleTestKernel
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
Differentiation under the compact radial testing integral for the first
manuscript modulation lemma.

On a fixed finite radius interval the transported test and its parameter
derivative are continuous.  Compactness of [-1,1] × [0,R] provides a uniform
integrable majorant, allowing differentiation under the integral with no
postulated parameter derivative.  The final -1 follows from the exact
radial integration-by-parts identity in ScaleTestKernel.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace HBL.Modulation

/-- The rescaled compact testing integral at an arbitrary radial profile. -/
def transportedRadialTestIntegral (R : ℝ) (zeta f : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..R, transportedRadialTest zeta a r * f r

/-- At a continuously differentiable profile, a local integrable bound
on the differentiated kernel justifies differentiation under the integral
and returns the exact derivative integral. -/
theorem transportedRadialTestIntegral_hasDerivAt_of_bound
    (R : ℝ) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (hf : ContDiff ℝ 1 f)
    (s : Set ℝ) (hs : s ∈ 𝓝 (0 : ℝ))
    (bound : ℝ → ℝ)
    (hbound :
      ∀ᵐ r ∂(volume : Measure ℝ),
        r ∈ Ι (0 : ℝ) R →
        ∀ a ∈ s,
          ‖transportedRadialTestDerivative zeta a r * f r‖ ≤ bound r)
    (hbound_int : IntervalIntegrable bound volume 0 R) :
    HasDerivAt (transportedRadialTestIntegral R zeta f)
      (∫ r in (0 : ℝ)..R,
        transportedRadialTestDerivative zeta 0 r * f r) 0 := by
  have hz : Continuous zeta := hzeta.continuous
  have hfcont : Continuous f := hf.continuous
  have hd_zeta : Continuous (deriv zeta) := hzeta.continuous_deriv_one
  have hFcont (a : ℝ) :
      Continuous (fun r : ℝ => transportedRadialTest zeta a r * f r) := by
    dsimp [transportedRadialTest]
    fun_prop
  have hFmeas :
      ∀ᶠ a in 𝓝 (0 : ℝ),
        AEStronglyMeasurable
          (fun r : ℝ => transportedRadialTest zeta a r * f r)
          ((volume : Measure ℝ).restrict (Ι (0 : ℝ) R)) :=
    Filter.Eventually.of_forall (fun a => (hFcont a).aestronglyMeasurable)
  have hF0int :
      IntervalIntegrable
        (fun r : ℝ => transportedRadialTest zeta 0 r * f r)
        volume 0 R :=
    (hFcont 0).intervalIntegrable (μ := volume) (a := 0) (b := R)
  have hDcont :
      Continuous (fun r : ℝ =>
        transportedRadialTestDerivative zeta 0 r * f r) := by
    dsimp [transportedRadialTestDerivative]
    fun_prop
  have hDmeas :
      AEStronglyMeasurable
        (fun r : ℝ => transportedRadialTestDerivative zeta 0 r * f r)
        ((volume : Measure ℝ).restrict (Ι (0 : ℝ) R)) :=
    hDcont.aestronglyMeasurable
  have hDiff :
      ∀ᵐ r ∂(volume : Measure ℝ),
        r ∈ Ι (0 : ℝ) R →
        ∀ a ∈ s,
          HasDerivAt
            (fun b : ℝ => transportedRadialTest zeta b r * f r)
            (transportedRadialTestDerivative zeta a r * f r) a :=
    Filter.Eventually.of_forall
      (fun r _ a _ =>
        (transportedRadialTest_hasDerivAt zeta hzeta a r).mul_const (f r))
  have hcalc :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := R)
      (F := fun a r => transportedRadialTest zeta a r * f r)
      (F' := fun a r => transportedRadialTestDerivative zeta a r * f r)
      (x₀ := (0 : ℝ)) (s := s) (bound := bound)
      hs hFmeas hF0int hDmeas hbound hbound_int hDiff
  change HasDerivAt (transportedRadialTestIntegral R zeta f)
    (∫ r in (0 : ℝ)..R, transportedRadialTestDerivative zeta 0 r * f r) 0
  exact hcalc.2

/-- Compactness of the two-dimensional parameter-radius rectangle produces
the dominated estimate required by the previous theorem automatically. -/
theorem transportedRadialTestIntegral_hasDerivAt
    (R : ℝ) (hR : 0 ≤ R) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (hf : ContDiff ℝ 1 f) :
    HasDerivAt (transportedRadialTestIntegral R zeta f)
      (∫ r in (0 : ℝ)..R,
        transportedRadialTestDerivative zeta 0 r * f r) 0 := by
  have hz : Continuous zeta := hzeta.continuous
  have hfcont : Continuous f := hf.continuous
  have hd_zeta : Continuous (deriv zeta) := hzeta.continuous_deriv_one
  have hJoint :
      Continuous (fun p : ℝ × ℝ =>
        transportedRadialTestDerivative zeta p.1 p.2 * f p.2) := by
    dsimp [transportedRadialTestDerivative]
    fun_prop
  have hCompact : IsCompact
      ((Icc (-1 : ℝ) 1) ×ˢ (Icc (0 : ℝ) R)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hCompact.exists_bound_of_continuousOn hJoint.continuousOn
  have hs : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := by
    exact Icc_mem_nhds (by norm_num) (by norm_num)
  have hBound :
      ∀ᵐ r ∂(volume : Measure ℝ),
        r ∈ Ι (0 : ℝ) R →
        ∀ a ∈ Icc (-1 : ℝ) 1,
          ‖transportedRadialTestDerivative zeta a r * f r‖ ≤ C := by
    apply Filter.Eventually.of_forall
    intro r hr a ha
    have hrI : r ∈ Icc (0 : ℝ) R := by
      rw [uIoc_of_le hR] at hr
      exact ⟨hr.1.le, hr.2⟩
    exact hC (a, r) ⟨ha, hrI⟩
  have hCint : IntervalIntegrable (fun _ : ℝ => C) volume 0 R :=
    continuous_const.intervalIntegrable (μ := volume) (a := 0) (b := R)
  exact transportedRadialTestIntegral_hasDerivAt_of_bound
    R zeta f hzeta hf (Icc (-1 : ℝ) 1) hs (fun _ => C)
    hBound hCint

/-- The normalized scale test has derivative -1 at logarithmic scale zero.
The conclusion is now a proof about the actual transported test integral:
neither the derivative nor the Jacobian is a hypothesis. -/
theorem transportedRadialTestIntegral_scale_normalized
    (R : ℝ) (hR : 0 ≤ R) (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta) (hf : ContDiff ℝ 1 f)
    (hzetaR : zeta R = 0)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * r * (f r / 2 + r * deriv f r)) = 1) :
    HasDerivAt (transportedRadialTestIntegral R zeta f) (-1) 0 := by
  have hDerivative :=
    transportedRadialTestIntegral_hasDerivAt R hR zeta f hzeta hf
  have hEval :
      (∫ r in (0 : ℝ)..R,
        transportedRadialTestDerivative zeta 0 r * f r) = -1 := by
    calc
      (∫ r in (0 : ℝ)..R,
          transportedRadialTestDerivative zeta 0 r * f r) =
        (∫ r in (0 : ℝ)..R,
          r * ((3 / 2 : ℝ) * zeta r + r * deriv zeta r) * f r) := by
            apply intervalIntegral.integral_congr
            intro r _
            simp [transportedRadialTestDerivative]
            ring
      _ = -1 :=
        transportedRadialTest_scale_normalized
          R zeta f hzeta hf hzetaR hNorm
  rw [hEval] at hDerivative
  exact hDerivative

end HBL.Modulation
