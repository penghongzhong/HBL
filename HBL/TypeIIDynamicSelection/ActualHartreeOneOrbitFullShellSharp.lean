import HBL.TypeIIDynamicSelection.ActualHartreeMomentRadiusDrift
import HBL.TypeIIDynamicSelection.ActualHartreeFullMovingCutoffResidualSharp
import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import Mathlib.Tactic

/-!
# One physically selected Hartree flow: complete moving shell residual gains 5/2

The original 3D inverse-square radial Hartree PDE prescribes
R(s)=4/(kappa_H*ell(s)*m(t(s))), where m is the TRUE all-radiation
quartic Hartree moment. From the actual physical Hartree PDE flux,
ell_s=-b ell, t_s=ell^2, we PROVE
  R_s/R-b = -ell^2*m'(t)/m(t).
Inserting this exact drift in the ALREADY STRICT full same-PDE
cutoff residual (transport + 3D radial Laplacian + full Riesz) and
using the cited Strauss radial lemma gives a uniform actual shell
O(ell^2 * sqrt(ell)) gain, not a generated atom assigned an order.

No parameter speed is postulated, no local replacement for the
quartic nonlocal Riesz integral, no chosen Type II concentration rate.

The real C2/nonlinear profile, all-weight residual, actual remote
and Kummer correction and full 2.12 elimination remain separate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The complete same-PDE physical Hartree moving overlap commutator
is O(ell^(5/2)) on its actual shell. The moment flux coefficient
is a genuine PDE derivative, rather than an artificial R_s input.

In particular, NO independent `R_s/R-b=O(ell^2)` is assumed.
The quartic envelope is DERIVED from Strauss and Linfty bounds. -/
theorem actual_Hartree_one_orbit_full_shell_from_PDE_moment_and_Strauss
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
        (ell s) ^ 2 * Real.sqrt (ell s) := by
  let m : ℝ := radialPhysicalQuarticMoment (z (time s))
  let R : ℝ → ℝ := actualPhysicalHartreeMomentRadius ell z time
  obtain ⟨Rs,hR,hDrift⟩ :=
    actual_Hartree_physical_moment_radius_drift_exact
      ell b z time s (actualMomentLaplacianFlux (z (time s)))
      hell hm hEll hClock hPDEMoment
  have hD : 0 ≤ (2 * (B ^ 4 + A ^ 4)) := by positivity
  have hQuartic : ∀ u : ℝ, 0 < u →
      ‖z (time s) u‖ ^ 4 ≤
        (2 * (B ^ 4 + A ^ 4)) * bubble u ^ 2 :=
    actual_Hartree_radial_quartic_envelope_from_Strauss
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
  have hRealRadius : R s = actualHartreeMomentCutoffRadius (ell s) m :=
    rfl
  have hShell' : actualHartreeMomentCutoffRadius (ell s) m ≤ r := by
    simpa only [R, actualPhysicalHartreeMomentRadius, m] using hShell
  have hShellRight' : r ≤ 2 * actualHartreeMomentCutoffRadius (ell s) m := by
    simpa only [R, actualPhysicalHartreeMomentRadius, m] using hShellRight
  obtain ⟨Cchi,C1,C2,hCchi,hC1,hC2,hSource⟩ :=
    actual_Hartree_full_physical_cutoff_PDE_shell_sharp
      R f (b s) omega s r Rs (ell s) m M B
      (2 * (B ^ 4 + A ^ 4))
      hR hRealRadius hfTime hfSpace hf2 hell hm hmBound
      hB hD (z (time s)) hz hfProfile hzSpace hzSecond
      hzAmp hzDerivBound hQuartic hShell' hShellRight'
  have hmatNonneg : 0 ≤ 2 * Cchi := by positivity
  have hfieldNonneg : 0 ≤ Real.sqrt (ell s) * B :=
    mul_nonneg (Real.sqrt_nonneg _) hB
  have hTimeBound :
      (2 * Cchi * |Rs / R s - b s|) *
        (Real.sqrt (ell s) * B) ≤
      (2 * Cchi * J * B) * (ell s) ^ 2 * Real.sqrt (ell s) := by
    calc
      _ ≤ (2 * Cchi * ((ell s) ^ 2 * J)) *
            (Real.sqrt (ell s) * B) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hmatNonneg)
          hfieldNonneg
      _ = (2 * Cchi * J * B) * (ell s) ^ 2 *
            Real.sqrt (ell s) := by ring
  refine ⟨Cchi,C1,C2,hCchi,hC1,hC2,?_⟩
  calc
    _ ≤ (2 * Cchi * |Rs / R s - b s|) *
            (Real.sqrt (ell s) * B) +
          ((2 * C1 * (hartreeKappa * M / 4) * B +
             (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
            2 * radialHartreeRowBoundConstant *
              (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
            (ell s) ^ 2 * Real.sqrt (ell s) := hSource
    _ ≤ (2 * Cchi * J * B) * (ell s) ^ 2 *
            Real.sqrt (ell s) +
          ((2 * C1 * (hartreeKappa * M / 4) * B +
             (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
            2 * radialHartreeRowBoundConstant *
              (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
            (ell s) ^ 2 * Real.sqrt (ell s) :=
        add_le_add_right hTimeBound _
    _ = ((2 * Cchi * J * B) +
          ((2 * C1 * (hartreeKappa * M / 4) * B +
             (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
            2 * radialHartreeRowBoundConstant *
              (2 * (B ^ 4 + A ^ 4)) * B ^ 3)) *
          (ell s) ^ 2 * Real.sqrt (ell s) := by ring

end HBL.TypeIIDynamicSelection
