import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalCorrectionNextLayer
import Mathlib.Tactic

/-!
# The actual correction remainder as a realized finite-profile residual atom

This file removes one use of the structural GeneratedTerm bookkeeping.
The atom value below is the ORIGINAL complex Hartree PDE residual difference
after subtracting the genuine moment-locked principal correction equation.
Its order is proved from the strict physical next-layer theorem; it is not
stored as an unsupported source-order label.

This is one realized residual class, not yet the whole finite-profile
realization required by revised manuscript 2.13.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ResidualLedger

def actualHartreeCorrectionResidualAtomValue
    (c0 c1 : ℝ → ℝ) (H : ℝ → ℝ → ℂ)
    (b omega db domega _m : ℝ → ℝ) (r s : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
      (fun t x => (actualMomentLockedCore (c1 t) x : ℂ) + H t x)
      (b s + db s) (omega s + domega s) s r -
    complexRadialRenormalizedResidual
      (fun t x => (actualMomentLockedCore (c0 t) x : ℂ))
      (b s) (omega s) s r -
    actualHartreeMomentLockedCorrectionPrincipalPart
      (c0 s) H (b s) (omega s) (db s) (domega s) s r

/-- The genuine correction remainder defines a realized residual atom.
All hypotheses are direct regularity/size properties of the same physical
paths.  The atom order is rho+kappa because the original PDE expression
has that bound, not by definition of a gain tag. -/
theorem actual_Hartree_correction_remainder_realized_atom
    (c0 c1 : ℝ → ℝ) (H : ℝ → ℝ → ℂ)
    (b omega db domega m : ℝ → ℝ)
    (r beta rhoStar rho Cspeed CHd CH : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hr : 0 < r)
    (hsame : ∀ s : ℝ, 1 ≤ s → c1 s = c0 s)
    (hc0 : ∀ s : ℝ, 1 ≤ s →
      HasDerivAt c0 (-(b s * c0 s) + m s) s)
    (hc1 : ∀ s : ℝ, 1 ≤ s →
      HasDerivAt c1 (-((b s + db s) * c1 s) + m s) s)
    (hcCore : ∀ s : ℝ, 1 ≤ s → |c0 s| ≤ 1)
    (hHtime : ∀ s : ℝ, 1 ≤ s →
      DifferentiableAt ℝ (fun t => H t r) s)
    (hHspace : ∀ s : ℝ, 1 ≤ s →
      ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hHsecond : ∀ s : ℝ, 1 ≤ s →
      DifferentiableAt ℝ (deriv (H s)) r)
    (hHmeas : ∀ s : ℝ, 1 ≤ s → Measurable (H s))
    (hSpeed : ∀ s : ℝ, 1 ≤ s →
      |db s| + |domega s| ≤ Cspeed * s ^ (-rho))
    (hDilation : ∀ s : ℝ, 1 ≤ s →
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hH : ∀ s : ℝ, 1 ≤ s → ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x) :
    ∃ atom : WeightedResidualAtom ℂ,
      atom.value =
        actualHartreeCorrectionResidualAtomValue c0 c1 H b omega db domega m r ∧
      atom.order = rho + actualHartreePhysicalKappa beta rhoStar ∧
      atom.constant =
        Cspeed * (CHd + CH) +
          63 * ((2 + 9 * monopoleRadialBoundConstant) + CH) ^ 5 * CH ^ 2 := by
  let kappa := actualHartreePhysicalKappa beta rhoStar
  let Mcore : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let C0 : ℝ :=
    Cspeed * (CHd + CH) +
      63 * (Mcore + CH) ^ 5 * CH ^ 2
  have hMcore : 0 ≤ Mcore := by
    dsimp [Mcore]
    have hm := monopoleRadialBoundConstant_pos.le
    linarith
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  let atom : WeightedResidualAtom ℂ :=
    { value := actualHartreeCorrectionResidualAtomValue
        c0 c1 H b omega db domega m r
      order := rho + kappa
      constant := C0
      constant_nonneg := hC0
      bound := by
        intro s hs
        have hNext :=
          actual_Hartree_moment_locked_correction_next_physical_layer
            c0 c1 H (b s) (omega s) (db s) (domega s) (m s)
            s r beta rhoStar rho Cspeed CHd CH
            hbeta hrhoStar hflat hs hrho hCs hCHd hCH hr
            (hsame s hs) (hc0 s hs) (hc1 s hs) (hcCore s hs)
            (hHtime s hs) (hHspace s hs) (hHsecond s hs)
            (hHmeas s hs) (hSpeed s hs) (hDilation s hs) (hH s hs)
        have hbpow : bubble r ^ 5 ≤ 1 := by
          have hb0 := bubble_nonneg r
          have hb1 := bubble_le_one r
          simpa only [one_pow] using pow_le_pow_left₀ hb0 hb1 5
        have hTaylorCoef :
            63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 ≤
              63 * (Mcore + CH) ^ 5 * CH ^ 2 := by
          have hcoef : 0 ≤ 63 * (Mcore + CH) ^ 5 * CH ^ 2 := by
            positivity
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hbpow hcoef
        have hCoef :
            Cspeed * (CHd + CH) +
                63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 ≤ C0 := by
          dsimp [C0]
          exact add_le_add_right hTaylorCoef _
        have hPow : 0 ≤ s ^ (-(rho + kappa)) :=
          Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ s) _
        have hBound := hNext.trans
          (mul_le_mul_of_nonneg_right hCoef hPow)
        simpa only [actualHartreeCorrectionResidualAtomValue, kappa, Mcore,
          C0] using hBound }
  refine ⟨atom, rfl, rfl, ?_⟩
  rfl

end HBL.TypeIIDynamicSelection
