import HBL.TypeIIDynamicSelection.ActualHartreeOneOrbitFullShellSharp
import HBL.KinematicTailEstimates
import Mathlib.Tactic

/-!
# Actual one-orbit full shell: derived positive renormalized-time gain

This file is deliberately a thin consumer of the already strict physical
moving-shell theorem.  It does not re-prove transport, the radial Laplacian
commutator, the nonlocal Hartree commutator, the moment-radius drift, or the
Strauss envelope.

The only new step is to convert the already proved factor
  ell(s)^2 * sqrt(ell(s))
into an integrable renormalized-time power under the visible bootstrap trap
  ell(s) <= s^(-beta), beta > 1/2.

The trap is an intermediate dynamical bootstrap hypothesis.  No final Type-II
rate is prescribed here; entry into and persistence in the trap still have to
be obtained from the actual dynamics.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The strict gain carried by the already verified ell^(5/2) full-shell
residual relative to the baseline integrable weight s^(-1). -/
def actualHartreeFullShellTimeGain (beta : ℝ) : ℝ :=
  5 * beta / 2 - 1

theorem actual_Hartree_full_shell_time_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    0 < actualHartreeFullShellTimeGain beta := by
  unfold actualHartreeFullShellTimeGain
  linarith

/-- Pure scale conversion for the exact factor occurring in the physical
moving-shell theorem.  The exponent is derived from the bootstrap trap. -/
theorem actual_Hartree_trapped_length_two_sqrt_positive_gain
    (s ell beta : ℝ) (hs : 1 ≤ s) (hell : 0 < ell)
    (htrap : ell ≤ s ^ (-beta)) :
    ell ^ 2 * Real.sqrt ell ≤
      s ^ (-1 - actualHartreeFullShellTimeGain beta) := by
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hb0 : 0 ≤ s ^ (-beta) := Real.rpow_nonneg hs0 _
  have hbpos : 0 < s ^ (-beta) := Real.rpow_pos_of_pos hspos _
  have hsq : ell ^ 2 ≤ (s ^ (-beta)) ^ 2 :=
    pow_le_pow_left₀ hell.le htrap 2
  have hsqrt : Real.sqrt ell ≤ Real.sqrt (s ^ (-beta)) :=
    Real.sqrt_le_sqrt htrap
  have hprod : ell ^ 2 * Real.sqrt ell ≤
      (s ^ (-beta)) ^ 2 * Real.sqrt (s ^ (-beta)) := by
    exact mul_le_mul hsq hsqrt (Real.sqrt_nonneg ell)
      (pow_nonneg hb0 2)
  have hfive :
      (s ^ (-beta)) ^ 2 * Real.sqrt (s ^ (-beta)) =
        (s ^ (-beta)) ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (s ^ (-beta)) 2,
      ← Real.rpow_add hbpos]
    norm_num
  calc
    ell ^ 2 * Real.sqrt ell ≤
        (s ^ (-beta)) ^ 2 * Real.sqrt (s ^ (-beta)) := hprod
    _ = (s ^ (-beta)) ^ (5 / 2 : ℝ) := hfive
    _ = s ^ ((-beta) * (5 / 2 : ℝ)) :=
      (Real.rpow_mul hs0 (-beta) (5 / 2 : ℝ)).symm
    _ = s ^ (-1 - actualHartreeFullShellTimeGain beta) := by
      congr 1
      unfold actualHartreeFullShellTimeGain
      ring

/-- The complete same-PDE physical moving-shell residual inherits a strict
positive, integrable renormalized-time order from the actual ell^(5/2)
estimate.  No constituent of the shell residual is replaced by an abstract
generated term. -/
theorem actual_Hartree_one_orbit_full_shell_positive_time_order
    (ell b time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (f : ℝ → ℝ → ℂ)
    (omega s r M B A J beta : ℝ)
    (hell : 0 < ell s)
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hClock : HasDerivAt time ((ell s) ^ 2) s)
    (hm : 0 < radialPhysicalQuarticMoment (z (time s)))
    (hmBound : radialPhysicalQuarticMoment (z (time s)) ≤ M)
    (hPDEMoment : HasDerivAt
       (fun t => radialPhysicalQuarticMoment (z t))
       (actualMomentLaplacianFlux (z (time s))) (time s))
    (hJ : 0 ≤ J)
    (hFlux : |actualMomentLaplacianFlux (z (time s))| ≤
       J * radialPhysicalQuarticMoment (z (time s)))
    (hfTime : DifferentiableAt ℝ (fun t => f t r) s)
    (hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x)
    (hf2 : DifferentiableAt ℝ (deriv (f s)) r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hz : Measurable (z (time s)))
    (hfProfile : f s = rescalePhysicalRadiation (ell s) (z (time s)))
    (hzSpace : ∀ x : ℝ, DifferentiableAt ℝ (z (time s)) (ell s * x))
    (hzSecond : DifferentiableAt ℝ (deriv (z (time s))) (ell s * r))
    (hzAmp : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B)
    (hzDerivBound : ‖deriv (z (time s)) (ell s * r)‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A)
    (hShell : actualPhysicalHartreeMomentRadius ell z time s ≤ r)
    (hShellRight : r ≤ 2 * actualPhysicalHartreeMomentRadius ell z time s)
    (hs : 1 ≤ s) (hbeta : 1 / 2 < beta)
    (htrap : ell s ≤ s ^ (-beta)) :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
      0 < actualHartreeFullShellTimeGain beta ∧
      ‖complexRadialRenormalizedResidual
          (fun t x =>
            actualOneLayerInnerOverlapCutoff
              (actualPhysicalHartreeMomentRadius ell z time t) x * f t x)
          (b s) omega s r -
        actualOneLayerInnerOverlapCutoff
          (actualPhysicalHartreeMomentRadius ell z time s) r *
          complexRadialRenormalizedResidual f (b s) omega s r‖ ≤
      ((2 * Cchi * J * B) +
        ((2 * C1 * (hartreeKappa * M / 4) * B +
           (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
          2 * radialHartreeRowBoundConstant *
            (2 * (B ^ 4 + A ^ 4)) * B ^ 3)) *
        s ^ (-1 - actualHartreeFullShellTimeGain beta) := by
  obtain ⟨Cchi, C1, C2, hCchi, hC1, hC2, hShellBound⟩ :=
    actual_Hartree_one_orbit_full_shell_from_PDE_moment_and_Strauss
      ell b time z f omega s r M B A J hell hEll hClock hm hmBound
      hPDEMoment hJ hFlux hfTime hfSpace hf2 hB hA hz hfProfile
      hzSpace hzSecond hzAmp hzDerivBound hStrauss hShell hShellRight
  have hGain := actual_Hartree_full_shell_time_gain_positive beta hbeta
  have hScale :=
    actual_Hartree_trapped_length_two_sqrt_positive_gain
      s (ell s) beta hs hell htrap
  let K : ℝ :=
    (2 * Cchi * J * B) +
      ((2 * C1 * (hartreeKappa * M / 4) * B +
         (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
        2 * radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4)) * B ^ 3)
  have hM : 0 < M := hm.trans_le hmBound
  have hkappa : 0 ≤ hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hrow : 0 ≤ radialHartreeRowBoundConstant :=
    radialHartreeRowBoundConstant_pos.le
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨Cchi, C1, C2, hCchi, hC1, hC2, hGain, ?_⟩
  calc
    _ ≤ K * (ell s) ^ 2 * Real.sqrt (ell s) := by
      simpa only [K] using hShellBound
    _ = K * ((ell s) ^ 2 * Real.sqrt (ell s)) := by ring
    _ ≤ K * s ^ (-1 - actualHartreeFullShellTimeGain beta) :=
      mul_le_mul_of_nonneg_left hScale hK

end HBL.TypeIIDynamicSelection
