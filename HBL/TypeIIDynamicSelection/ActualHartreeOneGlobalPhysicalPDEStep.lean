import HBL.TypeIIDynamicSelection.ActualHartreeOneGlobalCoreCorrectionNextLayer
import Mathlib.Tactic

/-!
# One genuine original Hartree PDE step after solving the linearized equation

This is the exact bridge from the SAME complex radial, inverse-square-quartic
nonlocal PDE linear-correction equation to the *corrected full PDE residual*.
The nonlinear remainder is bounded by the existing physical Taylor/speed
cross theorem, rather than postulated to have the next order.

The linearized PDE cancellation is an explicit unsolved mathematical input:
it must be produced by the actual matched four-zone Fredholm/Green packet.
In particular this theorem does not construct that packet, its parameter
Lipschitz estimate, or a physical Type-II solution. It does not close
revised original manuscript 2.13.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- For an actual ONE-global-background correction which solves the exact
linearized original Hartree PDE, the residual of the corrected field has
a strict one-step gain. The gain is not a premise; the explicit principal
PDE equation is the remaining physical solvability premise. -/
theorem actual_Hartree_full_PDE_next_gain_from_principal_cancellation
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega s r beta rhoStar rho Cspeed CHd CH M : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hs : 1 ≤ s)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hM : 0 ≤ M) (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x)
    (hPrincipal :
      actualHartreeOneGlobalCoreCorrectionPrincipal
        U H b omega db domega s r =
        -complexRadialRenormalizedResidual U b omega s r) :
    ‖complexRadialRenormalizedResidual
        (fun t x => U t x + H t x)
        (b + db) (omega + domega) s r‖ ≤
      (Cspeed * (CHd + CH) +
        63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
  have hNext :=
    actual_Hartree_one_global_core_correction_next_physical_layer
      U H b omega db domega
      s r beta rhoStar rho Cspeed CHd CH M
      hbeta hrhoStar hflat hs hrho hCs hCHd hCH hM hr
      hUtime hHtime hUspace hHspace hUsecond hHsecond
      hUmeas hHmeas hSpeed hDilation hUB hHB
  have hIdentity :
      actualHartreeOneGlobalCoreCorrectionRemainder
          U H b omega db domega s r =
        complexRadialRenormalizedResidual
          (fun t x => U t x + H t x)
          (b + db) (omega + domega) s r := by
    unfold actualHartreeOneGlobalCoreCorrectionRemainder
    rw [hPrincipal]
    ring
  rw [hIdentity] at hNext
  exact hNext


/-- The essential *noncircular* PDE reduction: the corrected ORIGINAL
nonlocal Hartree residual is bounded by its explicit LINEAR principal
defect plus a strictly higher-order actual nonlinear remainder.
No bound of any order is assumed for the principal defect. This is
the exact outstanding regional Fredholm/Kummer/moving-source task. -/
theorem actual_Hartree_full_PDE_controlled_by_actual_linear_principal_defect
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega s r beta rhoStar rho Cspeed CHd CH M : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hs : 1 ≤ s)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hM : 0 ≤ M) (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x) :
    ‖complexRadialRenormalizedResidual
        (fun t x => U t x + H t x)
        (b + db) (omega + domega) s r‖ ≤
      ‖complexRadialRenormalizedResidual U b omega s r +
          actualHartreeOneGlobalCoreCorrectionPrincipal
            U H b omega db domega s r‖ +
      (Cspeed * (CHd + CH) +
        63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
  have hNext :=
    actual_Hartree_one_global_core_correction_next_physical_layer
      U H b omega db domega
      s r beta rhoStar rho Cspeed CHd CH M
      hbeta hrhoStar hflat hs hrho hCs hCHd hCH hM hr
      hUtime hHtime hUspace hHspace hUsecond hHsecond
      hUmeas hHmeas hSpeed hDilation hUB hHB
  have hDecomp :
      complexRadialRenormalizedResidual
          (fun t x => U t x + H t x)
          (b + db) (omega + domega) s r =
        (complexRadialRenormalizedResidual U b omega s r +
          actualHartreeOneGlobalCoreCorrectionPrincipal
            U H b omega db domega s r) +
          actualHartreeOneGlobalCoreCorrectionRemainder
            U H b omega db domega s r := by
    unfold actualHartreeOneGlobalCoreCorrectionRemainder
    ring
  rw [hDecomp]
  exact (norm_add_le _ _).trans (add_le_add_right hNext _)

end HBL.TypeIIDynamicSelection
