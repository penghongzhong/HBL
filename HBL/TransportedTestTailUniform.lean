import HBL.TransportedTestTail
import HBL.RadialEnergyL2
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Uniform and Hilbert-space realization of the transported compact test tails.

For logarithmic scale a, the actual dual representer is
  Q_a(s) = integral_s^R K_a(r) dr,
where K_a is the transported compact radial test.  This file proves:
* joint continuity of the scale derivative of K_a;
* a uniform derivative bound on compact (a,r)-rectangles;
* C1 regularity of Q_a in the radial variable s;
* concrete L2 vectors for Q_a and for its candidate scale derivative.

The remaining step is to prove that a ↦ Q_a is differentiable in the L2 norm,
rather than only pointwise in s.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology Interval

namespace HBL.Modulation

/-- The scale derivative kernel is jointly continuous in scale and radius. -/
theorem transportedRadialTestDerivative_joint_continuous
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    Continuous (fun p : ℝ × ℝ =>
      transportedRadialTestDerivative zeta p.1 p.2) := by
  have hz : Continuous zeta := hzeta.continuous
  have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
  dsimp [transportedRadialTestDerivative]
  fun_prop

/-- On a compact scale-radius rectangle, the scale derivative kernel has
a uniform finite bound. -/
theorem transportedRadialTestDerivative_uniform_bound
    (A R : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Icc (-A) A, ∀ r ∈ Icc (0 : ℝ) R,
        ‖transportedRadialTestDerivative zeta a r‖ ≤ C := by
  have hcont := transportedRadialTestDerivative_joint_continuous zeta hzeta
  have hcompact :
      IsCompact ((Icc (-A) A) ×ˢ (Icc (0 : ℝ) R)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ :=
    hcompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro a ha r hr
  exact (hC₀ (a, r) ⟨ha, hr⟩).trans (le_max_left _ _)

/-- The scale derivative of the transported tail, before bundling in L2. -/
def transportedTestTailScaleDerivative
    (R : ℝ) (zeta : ℝ → ℝ) (a s : ℝ) : ℝ :=
  ∫ r in s..R, transportedRadialTestDerivative zeta a r

/-- The derivative tail is controlled by a uniform bound on its kernel. -/
theorem transportedTestTailScaleDerivative_abs_le
    (R C : ℝ) (zeta : ℝ → ℝ) (a s : ℝ)
    (hs0 : 0 ≤ s) (hsR : s ≤ R)
    (hC : ∀ r ∈ Icc (0 : ℝ) R,
      ‖transportedRadialTestDerivative zeta a r‖ ≤ C) :
    ‖transportedTestTailScaleDerivative R zeta a s‖ ≤ C * (R - s) := by
  have hbound :
      ∀ r ∈ Ι s R,
        ‖transportedRadialTestDerivative zeta a r‖ ≤ C := by
    intro r hr
    rw [uIoc_of_le hsR] at hr
    exact hC r ⟨hs0.trans hr.1.le, hr.2⟩
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := transportedRadialTestDerivative zeta a)
      hbound
  simpa [transportedTestTailScaleDerivative,
    abs_of_nonneg (sub_nonneg.mpr hsR)] using h

/-- For fixed scale, the derivative tail is C1 in the radial endpoint. -/
theorem transportedTestTailScaleDerivative_contDiff_one
    (R : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    ContDiff ℝ 1 (transportedTestTailScaleDerivative R zeta a) := by
  have hz : Continuous zeta := hzeta.continuous
  have hdz : Continuous (deriv zeta) := hzeta.continuous_deriv_one
  have hD : Continuous (transportedRadialTestDerivative zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) *
        ((3 / 2 : ℝ) * zeta (Real.exp a * r) +
          (Real.exp a * r) * deriv zeta (Real.exp a * r)) * r)
    fun_prop
  change ContDiff ℝ 1
    (fun s : ℝ => ∫ r in s..R, transportedRadialTestDerivative zeta a r)
  exact testTailPrimitive_contDiff_one R
    (transportedRadialTestDerivative zeta a) hD

/-- For fixed scale, the transported tail itself is C1 in the radial endpoint. -/
theorem transportedTestTail_contDiff_one_in_s
    (R : ℝ) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    ContDiff ℝ 1 (transportedTestTail R zeta a) := by
  have hz : Continuous zeta := hzeta.continuous
  have hK : Continuous (transportedRadialTest zeta a) := by
    change Continuous (fun r : ℝ =>
      Real.exp ((3 / 2 : ℝ) * a) * zeta (Real.exp a * r) * r)
    fun_prop
  change ContDiff ℝ 1
    (fun s : ℝ => ∫ r in s..R, transportedRadialTest zeta a r)
  exact testTailPrimitive_contDiff_one R
    (transportedRadialTest zeta a) hK

/-- The actual transported dual representer as a vector of the finite-radius
radial energy Hilbert space. -/
def transportedTestTailL2
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    RadialEnergyL2 R :=
  (continuous_memLp_restrict_Ioc 0 R hR
    (transportedTestTail R zeta a)
    (transportedTestTail_contDiff_one_in_s R zeta hzeta a).continuous 2).toLp
      (transportedTestTail R zeta a)

/-- The L2 transported representer agrees almost everywhere with its
classical tail integral. -/
theorem transportedTestTailL2_ae
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    (transportedTestTailL2 R hR zeta hzeta a : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)]
      transportedTestTail R zeta a := by
  exact (continuous_memLp_restrict_Ioc 0 R hR
    (transportedTestTail R zeta a)
    (transportedTestTail_contDiff_one_in_s R zeta hzeta a).continuous 2).coeFn_toLp

/-- Candidate L2 scale derivative of the transported representer. -/
def transportedTestTailScaleDerivativeL2
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    RadialEnergyL2 R :=
  (continuous_memLp_restrict_Ioc 0 R hR
    (transportedTestTailScaleDerivative R zeta a)
    (transportedTestTailScaleDerivative_contDiff_one R zeta hzeta a).continuous 2).toLp
      (transportedTestTailScaleDerivative R zeta a)

/-- The candidate derivative L2 vector agrees almost everywhere with the
classical scale-derivative tail. -/
theorem transportedTestTailScaleDerivativeL2_ae
    (R : ℝ) (hR : 0 ≤ R)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) (a : ℝ) :
    (transportedTestTailScaleDerivativeL2 R hR zeta hzeta a : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) R)]
      transportedTestTailScaleDerivative R zeta a := by
  exact (continuous_memLp_restrict_Ioc 0 R hR
    (transportedTestTailScaleDerivative R zeta a)
    (transportedTestTailScaleDerivative_contDiff_one R zeta hzeta a).continuous 2).coeFn_toLp

/-- The existing pointwise derivative theorem has exactly the newly bundled
candidate derivative as its scalar representative. -/
theorem transportedTestTail_hasDerivAt_zero_as_scaleDerivative
    (R s : ℝ) (hR : 0 ≤ R) (hs : 0 ≤ s)
    (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 1 zeta) :
    HasDerivAt (fun a : ℝ => transportedTestTail R zeta a s)
      (transportedTestTailScaleDerivative R zeta 0 s) 0 := by
  simpa [transportedTestTailScaleDerivative] using
    transportedTestTail_hasDerivAt_zero R s hR hs zeta hzeta

end HBL.Modulation
