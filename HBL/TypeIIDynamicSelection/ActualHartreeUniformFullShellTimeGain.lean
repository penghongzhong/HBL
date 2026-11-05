import HBL.TypeIIDynamicSelection.ActualHartreeUniformShellConstants
import HBL.TypeIIDynamicSelection.ActualHartreeOneOrbitFullShellTimeGain
import Mathlib.Tactic

/-!
# One fixed shell constant package gives a uniform positive time order

This file strengthens the already accepted pointwise shell-time theorem only
in quantifier order.  The three smooth-cutoff constants are selected before
the physical orbit, time, scale, radius and source data.  The physical
moment-radius drift and the same Strauss-produced quartic envelope are then
reused verbatim.

No Type-II rate is prescribed: the visible hypothesis ell(s) <= s^(-beta)
is the intermediate bootstrap trap, with beta > 1/2.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A single triple of fixed cutoff constants works for every application of
the genuine physical moving-shell residual, and the resulting coefficient is
independent of renormalized time. -/
theorem actual_Hartree_one_orbit_full_shell_uniform_positive_time_order :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (ell b time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
        (f : ℝ → ℝ → ℂ)
        (omega s r M B A J beta : ℝ),
      ∀ (_hell : 0 < ell s),
      ∀ (_hEll : HasDerivAt ell (-(b s * ell s)) s),
      ∀ (_hClock : HasDerivAt time ((ell s) ^ 2) s),
      ∀ (_hm : 0 < radialPhysicalQuarticMoment (z (time s))),
      ∀ (_hmBound : radialPhysicalQuarticMoment (z (time s)) ≤ M),
      ∀ (_hPDEMoment : HasDerivAt
        (fun t => radialPhysicalQuarticMoment (z t))
        (actualMomentLaplacianFlux (z (time s))) (time s)),
      ∀ (_hJ : 0 ≤ J),
      ∀ (_hFlux : |actualMomentLaplacianFlux (z (time s))| ≤
        J * radialPhysicalQuarticMoment (z (time s))),
      ∀ (_hfTime : DifferentiableAt ℝ (fun t => f t r) s),
      ∀ (_hfSpace : ∀ x : ℝ, DifferentiableAt ℝ (f s) x),
      ∀ (_hf2 : DifferentiableAt ℝ (deriv (f s)) r),
      ∀ (_hB : 0 ≤ B), ∀ (_hA : 0 ≤ A),
      ∀ (_hz : Measurable (z (time s))),
      ∀ (_hfProfile : f s = rescalePhysicalRadiation (ell s) (z (time s))),
      ∀ (_hzSpace : ∀ x : ℝ,
        DifferentiableAt ℝ (z (time s)) (ell s * x)),
      ∀ (_hzSecond : DifferentiableAt ℝ
        (deriv (z (time s))) (ell s * r)),
      ∀ (_hzAmp : ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B),
      ∀ (_hzDerivBound : ‖deriv (z (time s)) (ell s * r)‖ ≤ B),
      ∀ (_hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A),
      ∀ (_hShell : actualPhysicalHartreeMomentRadius ell z time s ≤ r),
      ∀ (_hShellRight :
        r ≤ 2 * actualPhysicalHartreeMomentRadius ell z time s),
      ∀ (_hs : 1 ≤ s), ∀ (_hbeta : 1 / 2 < beta),
      ∀ (_htrap : ell s ≤ s ^ (-beta)),
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
  obtain ⟨Cchi,C1,C2,hCchi,hC1,hC2,hUniform⟩ :=
    actual_Hartree_full_physical_cutoff_PDE_shell_uniform_constants
  refine ⟨Cchi,C1,C2,hCchi,hC1,hC2,?_⟩
  intro ell b time z f omega s r M B A J beta
    hell hEll hClock hm hmBound hPDEMoment hJ hFlux
    hfTime hfSpace hf2 hB hA hz hfProfile hzSpace hzSecond
    hzAmp hzDerivBound hStrauss hShell hShellRight hs hbeta htrap
  let m : ℝ := radialPhysicalQuarticMoment (z (time s))
  let R : ℝ → ℝ := actualPhysicalHartreeMomentRadius ell z time
  let D : ℝ := 2 * (B ^ 4 + A ^ 4)
  obtain ⟨Rs,hR,hDrift⟩ :=
    actual_Hartree_physical_moment_radius_drift_exact
      ell b z time s (actualMomentLaplacianFlux (z (time s)))
      hell hm hEll hClock hPDEMoment
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hQuartic : ∀ u : ℝ, 0 < u →
      ‖z (time s) u‖ ^ 4 ≤ D * bubble u ^ 2 := by
    dsimp [D]
    exact actual_Hartree_radial_quartic_envelope_from_Strauss
      (z (time s)) B A hB hA hzAmp hStrauss
  have hRatio :
      |Rs / R s - b s| ≤ (ell s) ^ 2 * J := by
    have hDrift' :
        Rs / R s - b s =
          -((ell s) ^ 2 *
            (actualMomentLaplacianFlux (z (time s)) / m)) := by
      simpa only [R, m] using hDrift
    rw [hDrift', abs_neg, abs_mul,
      abs_of_nonneg (sq_nonneg (ell s)), abs_div,
      abs_of_pos hm]
    exact mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hm).2 hFlux) (sq_nonneg (ell s))
  have hRadius : R s =
      actualHartreeMomentCutoffRadius (ell s) m := rfl
  have hShell' : actualHartreeMomentCutoffRadius (ell s) m ≤ r := by
    simpa only [R, actualPhysicalHartreeMomentRadius, m] using hShell
  have hShellRight' :
      r ≤ 2 * actualHartreeMomentCutoffRadius (ell s) m := by
    simpa only [R, actualPhysicalHartreeMomentRadius, m] using hShellRight
  have hRaw :=
    hUniform R f (b s) omega s r Rs (ell s) m M B D
      hR hRadius hfTime hfSpace hf2 hell hm hmBound hB hD
      (z (time s)) hz hfProfile hzSpace hzSecond hzAmp hzDerivBound
      hQuartic hShell' hShellRight'
  have hTimeBound :
      (2 * Cchi * |Rs / R s - b s|) *
          (Real.sqrt (ell s) * B) ≤
        (2 * Cchi * J * B) * (ell s) ^ 2 *
          Real.sqrt (ell s) := by
    have hfield : 0 ≤ Real.sqrt (ell s) * B :=
      mul_nonneg (Real.sqrt_nonneg _) hB
    have hcoef : 0 ≤ 2 * Cchi := by positivity
    calc
      _ ≤ (2 * Cchi * ((ell s) ^ 2 * J)) *
          (Real.sqrt (ell s) * B) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hcoef) hfield
      _ = _ := by ring
  let K : ℝ :=
    (2 * Cchi * J * B) +
      ((2 * C1 * (hartreeKappa * M / 4) * B +
         (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
        2 * radialHartreeRowBoundConstant * D * B ^ 3)
  have hM : 0 < M := hm.trans_le hmBound
  have hK : 0 ≤ K := by
    dsimp [K,D]
    have hrow := radialHartreeRowBoundConstant_pos
    unfold hartreeKappa
    positivity
  have hEllFactor :
      ‖complexRadialRenormalizedResidual
          (fun t x => actualOneLayerInnerOverlapCutoff (R t) x * f t x)
          (b s) omega s r -
        actualOneLayerInnerOverlapCutoff (R s) r *
          complexRadialRenormalizedResidual f (b s) omega s r‖ ≤
        K * ((ell s) ^ 2 * Real.sqrt (ell s)) := by
    calc
      _ ≤ (2 * Cchi * |Rs / R s - b s|) *
            (Real.sqrt (ell s) * B) +
          ((2 * C1 * (hartreeKappa * M / 4) * B +
            (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
            2 * radialHartreeRowBoundConstant * D * B ^ 3) *
              (ell s) ^ 2 * Real.sqrt (ell s) := hRaw
      _ ≤ (2 * Cchi * J * B) * (ell s) ^ 2 * Real.sqrt (ell s) +
          ((2 * C1 * (hartreeKappa * M / 4) * B +
            (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
            2 * radialHartreeRowBoundConstant * D * B ^ 3) *
              (ell s) ^ 2 * Real.sqrt (ell s) :=
        add_le_add_left hTimeBound _
      _ = K * ((ell s) ^ 2 * Real.sqrt (ell s)) := by
        dsimp [K]
        ring
  have hScale :=
    actual_Hartree_trapped_length_two_sqrt_positive_gain
      s (ell s) beta hs hell htrap
  have hFinal := hEllFactor.trans
    (mul_le_mul_of_nonneg_left hScale hK)
  simpa only [R, D, K] using hFinal

end HBL.TypeIIDynamicSelection
