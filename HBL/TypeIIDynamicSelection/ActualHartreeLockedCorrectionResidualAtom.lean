import HBL.TypeIIDynamicSelection.ActualHartreeCorrectionResidualAtom
import HBL.TypeIIDynamicSelection.ActualHartreeLockedPhysicalGain
import Mathlib.Tactic

/-!
# Realized moment-locked Hartree correction atom with the locked next-layer gain

Unlike a generated order tag, the atom value is literally the difference
of two physical nonlocal Hartree PDE residuals minus the genuine linearized
correction operator. The identity is derived from the same moment-locked
time jets, including zero amplitude. The nonlinear Taylor and modulation
cross terms are bounded with the locked physical minimum.

This module does not assert the existence of a full order-9/4 parametrix.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ResidualLedger

theorem actual_Hartree_correction_remainder_locked_realized_atom
    (c0 c1 : ℝ → ℝ) (H : ℝ → ℝ → ℂ)
    (b omega db domega m : ℝ → ℝ)
    (r beta rhoStar rho Cspeed CHd CH : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : actualHartreeLockedKappa beta rhoStar ≤ rho)
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
      atom.order = rho + actualHartreeLockedKappa beta rhoStar ∧
      atom.constant =
        Cspeed * (CHd + CH) +
          63 * ((2 + 9 * monopoleRadialBoundConstant) + CH) ^ 5 * CH ^ 2 := by
  let kappa := actualHartreeLockedKappa beta rhoStar
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
        have hExact :=
          actual_Hartree_moment_locked_correction_generated_remainder_exact
            c0 c1 H (b s) (omega s) (db s) (domega s) (m s)
            s r hr (hsame s hs) (hc0 s hs) (hc1 s hs)
            (hHtime s hs) (hHspace s hs) (hHsecond s hs)
        have hGen :=
          actual_Hartree_moment_locked_generated_remainder_next_locked_layer
            (c0 s) H (db s) (domega s) s r beta rhoStar rho
            Cspeed CHd CH hbeta hrhoStar hflat hs hrho
            (hcCore s hs) hCs hCHd hCH hr
            (hHmeas s hs) (hSpeed s hs)
            (hDilation s hs) (hH s hs)
        have hNext :
            ‖actualHartreeCorrectionResidualAtomValue
                c0 c1 H b omega db domega m r s‖ ≤
              (Cspeed * (CHd + CH) +
                63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
                s ^ (-(rho + kappa)) := by
          unfold actualHartreeCorrectionResidualAtomValue
          rw [hExact]
          simpa only [kappa, Mcore] using hGen
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
