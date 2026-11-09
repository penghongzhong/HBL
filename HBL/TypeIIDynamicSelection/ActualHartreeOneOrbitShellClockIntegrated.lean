import HBL.TypeIIDynamicSelection.ActualHartreeOneOrbitFullShellClockGain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Rate-free integration of the original Hartree physical-clock shell error

The original nonlocal Hartree shell has the true algebraic factor
ell(s)^2 sqrt(ell(s)), while the original physical clock satisfies
time'(s)=ell(s)^2. To integrate the shell error, one does NOT need an
externally stipulated ell(s)<=s^(-beta) bootstrap trap.

On a genuine differentiable modulation orbit, the actual physical
scale satisfies ell'(s)=-b(s)ell(s), so the two source factors
ell^2 sqrt(ell) and ell^2 are interval-integrable. The pointwise
0<ell<=1 estimate and FTC for the GENUINE physical clock give
  integral_{s0}^{s1} ell^2 sqrt(ell) ds <= time(s1)-time(s0).
This is the rate-free finite-slow-time budget for the original
full moving-shell Laplacian/transport/nonlocal Riesz commutator.

The existence of a finite physical terminal time, genuine small
terminal tail, and complete four-domain PDE feedback and source
recursion remain separate PDE consequences; this lemma does not
assume or conclude Type-II blowup speed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- The physically produced clock derivative absorbs the complete
ell^(5/2) shell factor after *actual* slow-time integration, without
assuming any renormalized s-power decay, if 0<ell<=1. -/
theorem actual_Hartree_shell_integrated_physical_clock_no_beta
    (ell b time : ℝ → ℝ) (s0 s1 : ℝ)
    (horder : s0 ≤ s1)
    (hEll : ∀ s ∈ Icc s0 s1,
      HasDerivAt ell (-(b s * ell s)) s)
    (hPositive : ∀ s ∈ Icc s0 s1, 0 < ell s)
    (hOne : ∀ s ∈ Icc s0 s1, ell s ≤ 1)
    (hClock : ∀ s ∈ Icc s0 s1,
      HasDerivAt time ((ell s) ^ 2) s) :
    (∫ s in s0..s1, (ell s) ^ 2 * Real.sqrt (ell s)) ≤
      time s1 - time s0 := by
  have hEllCont : ContinuousOn ell (Icc s0 s1) := by
    intro s hs
    exact (hEll s hs).continuousAt.continuousWithinAt
  have hSqCont : ContinuousOn
      (fun s : ℝ => (ell s) ^ 2) (Icc s0 s1) :=
    hEllCont.pow 2
  have hShellCont : ContinuousOn
      (fun s : ℝ => (ell s) ^ 2 * Real.sqrt (ell s))
      (Icc s0 s1) :=
    hSqCont.mul hEllCont.sqrt
  have hSqInt : IntervalIntegrable
      (fun s : ℝ => (ell s) ^ 2) volume s0 s1 :=
    hSqCont.intervalIntegrable_of_Icc horder
  have hShellInt : IntervalIntegrable
      (fun s : ℝ => (ell s) ^ 2 * Real.sqrt (ell s))
      volume s0 s1 :=
    hShellCont.intervalIntegrable_of_Icc horder
  have hPoint (s : ℝ) (hs : s ∈ Icc s0 s1) :
      (ell s) ^ 2 * Real.sqrt (ell s) ≤ (ell s) ^ 2 := by
    have hClockValue : deriv time s = (ell s) ^ 2 :=
      (hClock s hs).deriv
    have h := actual_Hartree_shell_ell_two_sqrt_le_true_clock_derivative
      ell time s (hPositive s hs) (hOne s hs) (hClock s hs)
    rwa [hClockValue] at h
  have hMono :=
    intervalIntegral.integral_mono_on horder
      hShellInt hSqInt (fun s hs => hPoint s hs)
  have hFTC :
      (∫ s in s0..s1, (ell s) ^ 2) =
        time s1 - time s0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hClock s (by simpa only [uIcc_of_le horder] using hs))
      hSqInt
  exact hMono.trans_eq hFTC

/-- Any nonnegative fixed actual Hartree shell coefficient inherits
the same physical-time budget. There is no free time-decay exponent. -/
theorem actual_Hartree_shell_integrated_fixed_coefficient_no_beta
    (ell b time : ℝ → ℝ) (s0 s1 C : ℝ)
    (horder : s0 ≤ s1) (hC : 0 ≤ C)
    (hEll : ∀ s ∈ Icc s0 s1,
      HasDerivAt ell (-(b s * ell s)) s)
    (hPositive : ∀ s ∈ Icc s0 s1, 0 < ell s)
    (hOne : ∀ s ∈ Icc s0 s1, ell s ≤ 1)
    (hClock : ∀ s ∈ Icc s0 s1,
      HasDerivAt time ((ell s) ^ 2) s) :
    (∫ s in s0..s1, C * ((ell s) ^ 2 * Real.sqrt (ell s))) ≤
      C * (time s1 - time s0) := by
  have hClockIntegral :=
    actual_Hartree_shell_integrated_physical_clock_no_beta
      ell b time s0 s1 horder hEll hPositive hOne hClock
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hClockIntegral hC

end HBL.TypeIIDynamicSelection
