import HBL.TypeIIDynamicSelection.ActualHartreeOneGlobalCoreCorrectionNextLayer
import HBL.TypeIIDynamicSelection.ActualHartreeShellWeightedNorm
import Mathlib.Tactic

/-!
# True nonlinear Hartree correction to the original conjugated shell-source norm

The exact original complex quartic nonlocal Hartree residual is evaluated
on a SINGLE evolving background and correction. Unlike a fixed-radius
WeightedResidualAtom, this proves membership in the ORIGINAL radial source
space for the literal physical residual cut to a moving shell.

The loss R^(13/4) is displayed and MUST NOT be silently suppressed. This
lemma is a shell estimate only, and the real physical four-piece field,
the weighted speed/dilation bounds and the PDE-derived clock/rate must
still be produced. No assumed Type-II rate or independent residual order.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Original spatial shell weighted Fredholm source for the TRUE nonlocal
same-global-background Hartree correction, with the full radial-conjugation
and shell-volume factor R^(13/4). -/
theorem actual_Hartree_one_global_core_conjugated_shell_weighted
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega s R beta rhoStar rho Cspeed CHd CH M : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hs : 1 ≤ s)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hR : 1 ≤ R)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd)
    (hCH : 0 ≤ CH) (hM : 0 ≤ M)
    (hUtime : ∀ r ∈ Icc R (2 * R),
      DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : ∀ r ∈ Icc R (2 * R),
      DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : ∀ r ∈ Icc R (2 * R),
      DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : ∀ r ∈ Icc R (2 * R),
      DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s))
    (hHmeas : Measurable (H s))
    (hResidualMeas : Measurable
      (fun r => actualHartreeOneGlobalCoreCorrectionRemainder
        U H b omega db domega s r))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation : ∀ r ∈ Icc R (2 * R),
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x) :
    let E : ℝ → ℂ :=
      fun r => actualHartreeOneGlobalCoreCorrectionRemainder
        U H b omega db domega s r
    let A := (Cspeed * (CHd + CH) +
      63 * (M + CH) ^ 5 * CH ^ 2) *
      s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar))
    InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
      innerWeightedNorm (7 / 4 : ℝ)
        (actualConjugatedShellMagnitude R E) ≤
          20 * R ^ (13 / 4 : ℝ) * A := by
  dsimp only
  let E : ℝ → ℂ := fun r =>
    actualHartreeOneGlobalCoreCorrectionRemainder
      U H b omega db domega s r
  let C0 : ℝ :=
    Cspeed * (CHd + CH) + 63 * (M + CH) ^ 5 * CH ^ 2
  let A : ℝ := C0 *
    s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar))
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hs0 : 0 ≤ s := by linarith
  have hPow : 0 ≤
      s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) :=
    Real.rpow_nonneg hs0 _
  have hA : 0 ≤ A := mul_nonneg hC0 hPow
  have hRpos : 0 < R := by linarith
  have hPoint (r : ℝ) (hr : r ∈ Icc R (2 * R)) :
      ‖E r‖ ≤ A := by
    have hrpos : 0 < r := hRpos.trans_le hr.1
    have hRaw :=
      actual_Hartree_one_global_core_correction_next_physical_layer
        U H b omega db domega s r beta rhoStar rho
        Cspeed CHd CH M
        hbeta hrhoStar hflat hs hrho hCs hCHd hCH hM hrpos
        (hUtime r hr) (hHtime r hr)
        hUspace hHspace (hUsecond r hr) (hHsecond r hr)
        hUmeas hHmeas hSpeed (hDilation r hr) hUB hHB
    have hBub : bubble r ^ 5 ≤ 1 := by
      have hb0 := bubble_nonneg r
      have hb1 := bubble_le_one r
      simpa only [one_pow] using pow_le_pow_left₀ hb0 hb1 5
    have hCoef :
        Cspeed * (CHd + CH) +
            63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 ≤ C0 := by
      dsimp [C0]
      have hnonneg : 0 ≤ 63 * (M + CH) ^ 5 * CH ^ 2 := by
        positivity
      have hh :=
        mul_le_mul_of_nonneg_left hBub hnonneg
      have hh2 :
          63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 ≤
            63 * (M + CH) ^ 5 * CH ^ 2 := by
        simpa only [mul_one] using hh
      exact add_le_add (le_refl _) hh2
    have hLe := hRaw.trans (mul_le_mul_of_nonneg_right hCoef hPow)
    simpa only [E, A, C0] using hLe
  have hShell :=
    actual_conjugated_shell_weighted_power_bound
      R A hR hA E (by simpa only [E] using hResidualMeas)
      (fun r hr => hPoint r hr)
  simpa only [E, A, C0] using hShell

end HBL.TypeIIDynamicSelection
