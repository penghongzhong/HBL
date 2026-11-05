import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualHartreeUniformFullShellTimeGain
import Mathlib.Tactic

/-!
# The complete moving-shell Hartree commutator as a realized residual atom

The value below is the ORIGINAL complex renormalized Hartree PDE difference
created by the true moment-selected moving cutoff.  The existing strict
uniform-shell theorem already includes the material transport, radial
Laplacian and complete nonlocal Hartree commutator.

Its order is therefore proved from the physical PDE estimate, not assigned
through GainCause.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.ResidualLedger
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeCutoffResidualValue
    (ell b time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (f : ℝ → ℝ → ℂ) (omega r s : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
      (fun t x =>
        actualOneLayerInnerOverlapCutoff
          (actualPhysicalHartreeMomentRadius ell z time t) x * f t x)
      (b s) omega s r -
    actualOneLayerInnerOverlapCutoff
      (actualPhysicalHartreeMomentRadius ell z time s) r *
      complexRadialRenormalizedResidual f (b s) omega s r

/-- The complete moving-shell PDE difference defines a genuine residual
atom of order 1+epsilon_shell.  All displayed hypotheses are primitive
physical regularity/trapping data for the same orbit. -/
theorem actual_Hartree_cutoff_realized_atom :
    ∃ Cchi C1 C2 : ℝ,
      0 < Cchi ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (ell b time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
        (f : ℝ → ℝ → ℂ)
        (omega r M B A J beta : ℝ),
      0 ≤ B → 0 ≤ A → 0 ≤ J →
      (∀ s : ℝ, 1 ≤ s → 0 < ell s) →
      (∀ s : ℝ, 1 ≤ s →
        HasDerivAt ell (-(b s * ell s)) s) →
      (∀ s : ℝ, 1 ≤ s →
        HasDerivAt time ((ell s) ^ 2) s) →
      (∀ s : ℝ, 1 ≤ s →
        0 < radialPhysicalQuarticMoment (z (time s))) →
      (∀ s : ℝ, 1 ≤ s →
        radialPhysicalQuarticMoment (z (time s)) ≤ M) →
      (∀ s : ℝ, 1 ≤ s →
        HasDerivAt
          (fun t => radialPhysicalQuarticMoment (z t))
          (actualMomentLaplacianFlux (z (time s))) (time s)) →
      (∀ s : ℝ, 1 ≤ s →
        |actualMomentLaplacianFlux (z (time s))| ≤
          J * radialPhysicalQuarticMoment (z (time s))) →
      (∀ s : ℝ, 1 ≤ s →
        DifferentiableAt ℝ (fun t => f t r) s) →
      (∀ s : ℝ, 1 ≤ s →
        ∀ x : ℝ, DifferentiableAt ℝ (f s) x) →
      (∀ s : ℝ, 1 ≤ s →
        DifferentiableAt ℝ (deriv (f s)) r) →
      (∀ s : ℝ, 1 ≤ s → Measurable (z (time s))) →
      (∀ s : ℝ, 1 ≤ s →
        f s = rescalePhysicalRadiation (ell s) (z (time s))) →
      (∀ s : ℝ, 1 ≤ s →
        ∀ x : ℝ, DifferentiableAt ℝ (z (time s)) (ell s * x)) →
      (∀ s : ℝ, 1 ≤ s →
        DifferentiableAt ℝ (deriv (z (time s))) (ell s * r)) →
      (∀ s : ℝ, 1 ≤ s →
        ∀ u : ℝ, 0 < u → ‖z (time s) u‖ ≤ B) →
      (∀ s : ℝ, 1 ≤ s →
        ‖deriv (z (time s)) (ell s * r)‖ ≤ B) →
      (∀ s : ℝ, 1 ≤ s →
        ∀ u : ℝ, 1 ≤ u → u * ‖z (time s) u‖ ≤ A) →
      (∀ s : ℝ, 1 ≤ s →
        actualPhysicalHartreeMomentRadius ell z time s ≤ r) →
      (∀ s : ℝ, 1 ≤ s →
        r ≤ 2 * actualPhysicalHartreeMomentRadius ell z time s) →
      1 / 2 < beta →
      (∀ s : ℝ, 1 ≤ s → ell s ≤ s ^ (-beta)) →
      ∃ atom : WeightedResidualAtom ℂ,
        atom.value = actualHartreeCutoffResidualValue ell b time z f omega r ∧
        atom.order = 1 + actualHartreeFullShellTimeGain beta ∧
        atom.constant =
          (2 * Cchi * J * B) +
            ((2 * C1 * (hartreeKappa * M / 4) * B +
               (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
              2 * radialHartreeRowBoundConstant *
                (2 * (B ^ 4 + A ^ 4)) * B ^ 3) := by
  obtain ⟨Cchi,C1,C2,hCchi,hC1,hC2,hShell⟩ :=
    actual_Hartree_one_orbit_full_shell_uniform_positive_time_order
  refine ⟨Cchi,C1,C2,hCchi,hC1,hC2,?_⟩
  intro ell b time z f omega r M B A J beta
    hB hA hJ hell hEll hClock hm hmBound hPDEMoment hFlux
    hfTime hfSpace hf2 hz hfProfile hzSpace hzSecond hzAmp
    hzDerivBound hStrauss hShellLeft hShellRight hbeta htrap
  let C0 : ℝ :=
    (2 * Cchi * J * B) +
      ((2 * C1 * (hartreeKappa * M / 4) * B +
         (C2 + 2 * C1) * (hartreeKappa * M / 4) ^ 2 * B) +
        2 * radialHartreeRowBoundConstant *
          (2 * (B ^ 4 + A ^ 4)) * B ^ 3)
  have hM : 0 < M := by
    have hp := hm 1 (by norm_num)
    have hb := hmBound 1 (by norm_num)
    exact hp.trans_le hb
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    have hrow := radialHartreeRowBoundConstant_pos
    unfold hartreeKappa
    positivity
  let atom : WeightedResidualAtom ℂ :=
    { value := actualHartreeCutoffResidualValue ell b time z f omega r
      order := 1 + actualHartreeFullShellTimeGain beta
      constant := C0
      constant_nonneg := hC0
      bound := by
        intro s hs
        have h :=
          hShell ell b time z f (omega) s r M B A J beta
            (hell s hs) (hEll s hs) (hClock s hs)
            (hm s hs) (hmBound s hs) (hPDEMoment s hs)
            hJ (hFlux s hs) (hfTime s hs) (hfSpace s hs)
            (hf2 s hs) hB hA (hz s hs) (hfProfile s hs)
            (hzSpace s hs) (hzSecond s hs) (hzAmp s hs)
            (hzDerivBound s hs) (hStrauss s hs)
            (hShellLeft s hs) (hShellRight s hs)
            hs hbeta (htrap s hs)
        have hexp :
            -1 - actualHartreeFullShellTimeGain beta =
              -(1 + actualHartreeFullShellTimeGain beta) := by ring
        rw [hexp] at h
        simpa only [actualHartreeCutoffResidualValue, C0] using h }
  refine ⟨atom, rfl, rfl, ?_⟩
  rfl

theorem actual_Hartree_cutoff_realized_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    1 < 1 + actualHartreeFullShellTimeGain beta := by
  have h := actual_Hartree_full_shell_time_gain_positive beta hbeta
  linarith

end HBL.TypeIIDynamicSelection
