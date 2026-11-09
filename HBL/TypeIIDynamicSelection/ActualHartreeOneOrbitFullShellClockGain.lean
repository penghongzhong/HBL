import HBL.TypeIIDynamicSelection.ActualHartreeOneOrbitFullShellSharp
import Mathlib.Tactic

/-!
# A rate-free physical-clock gain for the SAME 3D nonlocal Hartree PDE shell

From the genuine PDE source, the full moving overlap shell commutator
(transport + 3D Laplacian + complete quartic Riesz) is bounded by
C ell(s)^2 sqrt(ell(s)); its radius drift is the true flux expression.

The ACTUAL renormalized physical clock satisfies t_s=ell(s)^2.
For 0<ell(s)<=1, the source factor satisfies
      ell(s)^2 sqrt(ell(s)) <= t_s.
This eliminates the externally stipulated renormalized-time decay trap
ell(s)<=s^{-beta} entirely for this shell: the shell error is dominated
by the genuine physical clock's positive derivative.

This is a time-slice and physical-clock domination. Passing to a
small time-TAIL of the full four-domain residual still requires
a controlled finite physical time horizon, absolute continuity,
the Kummer/remote regions, and a real finite nonlinear recursion.
This proof does NOT assume or conclude a Type-II blowup rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original clock identity gives a rate-free upper bound for the
shell weight.  No beta, no s^(-rho) trap, and no assumed blowup rate. -/
theorem actual_Hartree_shell_ell_two_sqrt_le_true_clock_derivative
    (ell time : ℝ → ℝ) (s : ℝ)
    (_hell : 0 < ell s) (hOne : ell s ≤ 1)
    (hClock : HasDerivAt time ((ell s) ^ 2) s) :
    (ell s) ^ 2 * Real.sqrt (ell s) ≤ deriv time s := by
  have hSqrt : Real.sqrt (ell s) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hOne
  calc
    (ell s) ^ 2 * Real.sqrt (ell s) ≤
        (ell s) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hSqrt (pow_nonneg hell.le 2)
    _ = (ell s) ^ 2 := by ring
    _ = deriv time s := (hClock.deriv).symm

/-- Same original quartic Hartree PDE orbit: the *complete genuine*
moving-shell commutator is bounded by the ACTUAL physical-clock derivative,
not a postulated power of the renormalized time. -/
theorem actual_Hartree_one_orbit_full_shell_clock_integrable_density
    (ell b time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (f : ℝ → ℝ → ℂ)
    (omega s r M B A J : ℝ)
    (hell : 0 < ell s) (hOne : ell s ≤ 1)
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
    (hShellRight : r ≤ 2 * actualPhysicalHartreeMomentRadius ell z time s) :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
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
        deriv time s := by
  obtain ⟨Cchi, C1, C2, hCchi, hC1, hC2, hPDE⟩ :=
    actual_Hartree_one_orbit_full_shell_from_PDE_moment_and_Strauss
      ell b time z f omega s r M B A J hell hEll hClock hm hmBound
      hPDEMoment hJ hFlux hfTime hfSpace hf2 hB hA hz hfProfile
      hzSpace hzSecond hzAmp hzDerivBound hStrauss hShell hShellRight
  have hClockBudget :=
    actual_Hartree_shell_ell_two_sqrt_le_true_clock_derivative
      ell time s hell hOne hClock
  let C : ℝ :=
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
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨Cchi, C1, C2, hCchi, hC1, hC2, ?_⟩
  calc
    _ ≤ C * ((ell s) ^ 2 * Real.sqrt (ell s)) := by
      simpa only [C, mul_assoc] using hPDE
    _ ≤ C * deriv time s :=
      mul_le_mul_of_nonneg_left hClockBudget hC
    _ = _ := by rfl

/-- Stronger rate-free clock-gain identity: the *full physical Hartree*
nonlocal shell remainder has a factor √ell relative to dt/ds. This has
NO upper scale, no s-decay trap, and no prescribed Type-II exponent.
To turn its small factor into an asymptotic statement one must still
derive ell→0 and clock integrability from the original PDE trajectory. -/
theorem actual_Hartree_one_orbit_full_shell_clock_sqrt_gain
    (ell b time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (f : ℝ → ℝ → ℂ)
    (omega s r M B A J : ℝ)
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
    (hShellRight : r ≤ 2 * actualPhysicalHartreeMomentRadius ell z time s) :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
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
        (Real.sqrt (ell s) * deriv time s) := by
  obtain ⟨Cchi, C1, C2, hCchi, hC1, hC2, hPDE⟩ :=
    actual_Hartree_one_orbit_full_shell_from_PDE_moment_and_Strauss
      ell b time z f omega s r M B A J hell hEll hClock hm hmBound
      hPDEMoment hJ hFlux hfTime hfSpace hf2 hB hA hz hfProfile
      hzSpace hzSecond hzAmp hzDerivBound hStrauss hShell hShellRight
  have hClockExact :
      (ell s) ^ 2 * Real.sqrt (ell s) =
        Real.sqrt (ell s) * deriv time s := by
    rw [hClock.deriv]
    ring
  let C : ℝ :=
    (2 * Cchi * J * B) +
      ((2 * C1 * (hartreeKappa * M / 4) * B +
          (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
        2 * radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4)) * B ^ 3)
  refine ⟨Cchi, C1, C2, hCchi, hC1, hC2, ?_⟩
  calc
    _ ≤ C * ((ell s) ^ 2 * Real.sqrt (ell s)) := by
      simpa only [C, mul_assoc] using hPDE
    _ = C * (Real.sqrt (ell s) * deriv time s) := by
      rw [hClockExact]
    _ = _ := by ring

end HBL.TypeIIDynamicSelection
