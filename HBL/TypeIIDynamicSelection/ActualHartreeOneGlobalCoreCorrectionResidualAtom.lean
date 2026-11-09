import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualHartreeOneGlobalCoreCorrectionNextLayer
import Mathlib.Tactic

/-!
# Genuine same-global-background Hartree correction residual atom

The old correction atom equated two core parameter paths globally while
assigning incompatible modulation speeds. This revised producer uses a
single physical background U(s,r), its true correction H(s,r), and the
literal complete quartic nonlocal Hartree residual. No global equality
of distinct core paths or independent next-order estimate is assumed.

The principal term is explicitly the original PDE linearization and
modulation-speed increment on U; the complete Hartree nonlinear
remainder gains order from the true quadratic Taylor/speed-cross estimates.
This statement does not produce the physical four-region correction nor
claim the principal Hartree equation already solved.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole
open HBL.Profile.ResidualLedger

/-- An original nonlocal Hartree PDE residual atom from ONE global
background and one correction. Unlike the earlier moment-locked
two-core comparison, no condition forces the scale correction to vanish. -/
theorem actual_Hartree_one_global_core_correction_realized_atom
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega : ℝ → ℝ)
    (r beta rhoStar rho Cspeed CHd CH M : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hM : 0 ≤ M) (hr : 0 < r)
    (hUtime : ∀ s : ℝ, 1 ≤ s →
      DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : ∀ s : ℝ, 1 ≤ s →
      DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ s : ℝ, 1 ≤ s →
      ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ s : ℝ, 1 ≤ s →
      ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : ∀ s : ℝ, 1 ≤ s →
      DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : ∀ s : ℝ, 1 ≤ s →
      DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : ∀ s : ℝ, 1 ≤ s → Measurable (U s))
    (hHmeas : ∀ s : ℝ, 1 ≤ s → Measurable (H s))
    (hSpeed : ∀ s : ℝ, 1 ≤ s →
      |db s| + |domega s| ≤ Cspeed * s ^ (-rho))
    (hDilation : ∀ s : ℝ, 1 ≤ s →
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hUB : ∀ s : ℝ, 1 ≤ s → ∀ x : ℝ, 0 < x →
      ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ s : ℝ, 1 ≤ s → ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x) :
    ∃ atom : WeightedResidualAtom ℂ,
      atom.value =
        (fun s => actualHartreeOneGlobalCoreCorrectionRemainder
          U H (b s) (omega s) (db s) (domega s) s r) ∧
      atom.order = rho + actualHartreePhysicalKappa beta rhoStar ∧
      atom.constant =
        Cspeed * (CHd + CH) +
          63 * (M + CH) ^ 5 * CH ^ 2 := by
  let kappa := actualHartreePhysicalKappa beta rhoStar
  let C0 := Cspeed * (CHd + CH) +
      63 * (M + CH) ^ 5 * CH ^ 2
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  let atom : WeightedResidualAtom ℂ :=
    { value := fun s =>
        actualHartreeOneGlobalCoreCorrectionRemainder
          U H (b s) (omega s) (db s) (domega s) s r
      order := rho + kappa
      constant := C0
      constant_nonneg := hC0
      bound := by
        intro s hs
        have hNext :=
          actual_Hartree_one_global_core_correction_next_physical_layer
            U H (b s) (omega s) (db s) (domega s)
            s r beta rhoStar rho Cspeed CHd CH M
            hbeta hrhoStar hflat hs hrho hCs hCHd hCH
            hM hr (hUtime s hs) (hHtime s hs)
            (hUspace s hs) (hHspace s hs)
            (hUsecond s hs) (hHsecond s hs)
            (hUmeas s hs) (hHmeas s hs)
            (hSpeed s hs) (hDilation s hs)
            (hUB s hs) (hHB s hs)
        have hbpow : bubble r ^ 5 ≤ 1 := by
          have hb0 := bubble_nonneg r
          have hb1 := bubble_le_one r
          simpa only [one_pow] using pow_le_pow_left₀ hb0 hb1 5
        have hTaylorCoef :
            63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 ≤
              63 * (M + CH) ^ 5 * CH ^ 2 := by
          have hcoef : 0 ≤ 63 * (M + CH) ^ 5 * CH ^ 2 := by
            positivity
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hbpow hcoef
        have hCoef :
            Cspeed * (CHd + CH) +
              63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 ≤ C0 := by
          dsimp [C0]
          exact add_le_add_right hTaylorCoef _
        have hPow : 0 ≤ s ^ (-(rho + kappa)) :=
          Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ s) _
        have hBound := hNext.trans
          (mul_le_mul_of_nonneg_right hCoef hPow)
        simpa only [kappa, C0] using hBound }
  refine ⟨atom, rfl, rfl, ?_⟩
  rfl

end HBL.TypeIIDynamicSelection
