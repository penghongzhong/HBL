import HBL.TypeIIDynamicSelection.ActualHartreeUniformFullShellClockNoBeta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Genuine 3D quartic Hartree moving-shell residual: rate-free time integral

The true PDE moment determines the moving shell, and the entire original
Hartree nonlocal commutator appears on the left, not a symbolic error atom.
The cutoff constants are universal and precede the orbit, time and radius.

The only independent temporal regularity input is continuity of the *actual*
complex residual along a moving shell trajectory; it is not an assumed
integrable source envelope or decay rate. The same physical modulation
identities supply t'(s)=ell(s)^2, with 0<ell<=1. Hence the original Hartree
shell is integrably dominated by the physical time increment, without
assuming ell(s)<=s^(-beta).

This only treats the actual overlap shell. A finite terminal physical time,
full four-region Hartree PDE residual, parameter Lipschitz, genuine finite
profile recursion and the dynamically selected Type-II rate are not shown.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The true radial quartic Hartree moving-shell residual, integrated along
any physical shell trajectory, is dominated by its *original* physical
clock increment. The constants are fixed independently of the trajectory.
The exact residual continuity is a regularity premise, not a decay premise. -/
theorem actual_Hartree_one_orbit_uniform_full_shell_clock_integral
    (ell b time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (f : ℝ → ℝ → ℂ) (omega r : ℝ → ℝ)
    (s0 s1 M B A J : ℝ)
    (horder : s0 ≤ s1)
    (hEllPos : ∀ s ∈ Icc s0 s1, 0 < ell s)
    (hOne : ∀ s ∈ Icc s0 s1, ell s ≤ 1)
    (hEll : ∀ s ∈ Icc s0 s1,
      HasDerivAt ell (-(b s * ell s)) s)
    (hClock : ∀ s ∈ Icc s0 s1,
      HasDerivAt time ((ell s) ^ 2) s)
    (hm : ∀ s ∈ Icc s0 s1,
      0 < radialPhysicalQuarticMoment (z (time s)))
    (hmBound : ∀ s ∈ Icc s0 s1,
      radialPhysicalQuarticMoment (z (time s)) ≤ M)
    (hPDEMoment : ∀ s ∈ Icc s0 s1,
      HasDerivAt
        (fun t => radialPhysicalQuarticMoment (z t))
        (actualMomentLaplacianFlux (z (time s))) (time s))
    (hJ : 0 ≤ J)
    (hFlux : ∀ s ∈ Icc s0 s1,
      |actualMomentLaplacianFlux (z (time s))| ≤
        J * radialPhysicalQuarticMoment (z (time s)))
    (hfTime : ∀ s ∈ Icc s0 s1,
      DifferentiableAt ℝ (fun t => f t (r s)) s)
    (hfSpace : ∀ s ∈ Icc s0 s1,
      ∀ x : ℝ, DifferentiableAt ℝ (f s) x)
    (hf2 : ∀ s ∈ Icc s0 s1,
      DifferentiableAt ℝ (deriv (f s)) (r s))
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hz : ∀ s ∈ Icc s0 s1, Measurable (z (time s)))
    (hfProfile : ∀ s ∈ Icc s0 s1,
      f s = rescalePhysicalRadiation (ell s) (z (time s)))
    (hzSpace : ∀ s ∈ Icc s0 s1,
      ∀ x : ℝ, DifferentiableAt ℝ (z (time s)) (ell s * x))
    (hzSecond : ∀ s ∈ Icc s0 s1,
      DifferentiableAt ℝ (deriv (z (time s))) (ell s * r s))
    (hzAmp : ∀ s ∈ Icc s0 s1, ∀ u : ℝ,
      0 < u → ‖z (time s) u‖ ≤ B)
    (hzDerivBound : ∀ s ∈ Icc s0 s1,
      ‖deriv (z (time s)) (ell s * r s)‖ ≤ B)
    (hStrauss : ∀ s ∈ Icc s0 s1, ∀ u : ℝ,
      1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hShell : ∀ s ∈ Icc s0 s1,
      actualPhysicalHartreeMomentRadius ell z time s ≤ r s)
    (hShellRight : ∀ s ∈ Icc s0 s1,
      r s ≤ 2 * actualPhysicalHartreeMomentRadius ell z time s)
    (hResidualContinuous : ContinuousOn
      (fun s : ℝ =>
        complexRadialRenormalizedResidual
          (fun t x =>
            actualOneLayerInnerOverlapCutoff
              (actualPhysicalHartreeMomentRadius ell z time t) x * f t x)
          (b s) (omega s) s (r s) -
        actualOneLayerInnerOverlapCutoff
          (actualPhysicalHartreeMomentRadius ell z time s) (r s) *
          complexRadialRenormalizedResidual f (b s) (omega s) s (r s))
      (Icc s0 s1)) :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
      (∫ s in s0..s1,
        ‖complexRadialRenormalizedResidual
          (fun t x =>
            actualOneLayerInnerOverlapCutoff
              (actualPhysicalHartreeMomentRadius ell z time t) x * f t x)
          (b s) (omega s) s (r s) -
        actualOneLayerInnerOverlapCutoff
          (actualPhysicalHartreeMomentRadius ell z time s) (r s) *
          complexRadialRenormalizedResidual f (b s) (omega s) s (r s)‖)
       ≤ ((2 * Cchi * J * B) +
          ((2 * C1 * (hartreeKappa * M / 4) * B +
            (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
            2 * radialHartreeRowBoundConstant *
              (2 * (B ^ 4 + A ^ 4)) * B ^ 3)) *
              (time s1 - time s0) := by
  obtain ⟨Cchi, C1, C2, hCchi, hC1, hC2, hUniform⟩ :=
    actual_Hartree_one_orbit_full_shell_uniform_clock_no_beta
  refine ⟨Cchi, C1, C2, hCchi, hC1, hC2, ?_⟩
  let K : ℝ :=
    ((2 * Cchi * J * B) +
      ((2 * C1 * (hartreeKappa * M / 4) * B +
        (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
        2 * radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4)) * B ^ 3))
  let E : ℝ → ℝ := fun s =>
    ‖complexRadialRenormalizedResidual
        (fun t x =>
          actualOneLayerInnerOverlapCutoff
            (actualPhysicalHartreeMomentRadius ell z time t) x * f t x)
        (b s) (omega s) s (r s) -
      actualOneLayerInnerOverlapCutoff
        (actualPhysicalHartreeMomentRadius ell z time s) (r s) *
        complexRadialRenormalizedResidual f (b s) (omega s) s (r s)‖
  have hEllCont : ContinuousOn ell (Icc s0 s1) := by
    intro s hs
    exact (hEll s hs).continuousAt.continuousWithinAt
  have hSqInt : IntervalIntegrable
      (fun s : ℝ => (ell s) ^ 2) volume s0 s1 :=
    (hEllCont.pow 2).intervalIntegrable_of_Icc horder
  have hDomInt : IntervalIntegrable
      (fun s : ℝ => K * (ell s) ^ 2) volume s0 s1 :=
    hSqInt.const_mul K
  have hErrInt : IntervalIntegrable E volume s0 s1 := by
    exact (hResidualContinuous.norm).intervalIntegrable_of_Icc horder
  have hPoint (s : ℝ) (hs : s ∈ Icc s0 s1) :
      E s ≤ K * (ell s) ^ 2 := by
    have hBound :=
      hUniform ell b time z f (omega s) s (r s) M B A J
        (hEllPos s hs) (hEll s hs) (hClock s hs)
        (hm s hs) (hmBound s hs) (hPDEMoment s hs)
        hJ (hFlux s hs) (hfTime s hs)
        (hfSpace s hs) (hf2 s hs) hB hA
        (hz s hs) (hfProfile s hs) (hzSpace s hs)
        (hzSecond s hs) (hzAmp s hs)
        (hzDerivBound s hs) (hStrauss s hs)
        (hShell s hs) (hShellRight s hs) (hOne s hs)
    rw [(hClock s hs).deriv] at hBound
    simpa only [E, K] using hBound
  have hMono := intervalIntegral.integral_mono_on horder
    hErrInt hDomInt (fun s hs => hPoint s hs)
  have hFTC : (∫ s in s0..s1, (ell s) ^ 2) =
      time s1 - time s0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hClock s
        (by simpa only [uIcc_of_le horder] using hs))
      hSqInt
  calc
    (∫ s in s0..s1, E s) ≤
        (∫ s in s0..s1, K * (ell s) ^ 2) := hMono
    _ = K * (∫ s in s0..s1, (ell s) ^ 2) :=
      intervalIntegral.integral_const_mul _ _ _
    _ = K * (time s1 - time s0) := by rw [hFTC]
