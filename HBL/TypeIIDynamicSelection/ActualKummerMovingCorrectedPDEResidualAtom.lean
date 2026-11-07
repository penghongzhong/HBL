import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualKummerMovingCorrectedPhysicalPDENextLockedGain
import Mathlib.Tactic

/-!
# Realized moving Kummer PDE residual on the corrected Hartree background

This atom is the ORIGINAL nonlocal complex renormalized Hartree PDE residual
difference between the common time-dependent physical background and that
same corrected background V_c+Z_ell+H with the concrete moving Kummer tail.

Its bound follows from the same PDE's full quartic density feedback and the
actual sqrt-clock radius/time estimates.  No arbitrary generated-term order,
free boundary jet, artificial PDE forcing, or prescribed Type-II rate occurs.

It is a genuine realized new-layer producer; it does not yet classify every
source of the full finite physical profile.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.ResidualLedger
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Original full complex Hartree PDE residual for the moving physical
replacement tail evaluated on the common moment-locked physical orbit. -/
def actualHartreeMovingCorrectedKummerTruePDEResidualValue
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z H : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ) (r s : ℝ) : ℂ :=
  let U : ℝ → ℝ → ℂ := fun t y =>
    (actualMomentLockedCore (c t) y : ℂ) +
      rescalePhysicalRadiation (ell t) (z (time t)) y + H t y
  complexRadialRenormalizedResidual
      (fun t y => U t y + actualKummerPhysicalOuterRepair a R p q t y)
      (b s) (omega s) s r -
    complexRadialRenormalizedResidual U (b s) (omega s) s r

/-- Full nonlinear PDE realization at order rho + locked kappa, with the
actual selected tail jet and physical radiation bounds left as explicit
analytic inputs. In particular the bound is a conclusion, not an atom tag. -/
theorem actual_Hartree_moving_corrected_Kummer_true_PDE_locked_realized_atom
    (a ell c time : ℝ → ℝ) (R : ℝ)
    (p q : ℝ → ℂ) (z H : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ)
    (r B A CH beta rhoStar rho CX CD : ℝ)
    (ha : ∀ t : ℝ, 0 < a t)
    (haCont : Continuous a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (hCX : 0 ≤ CX) (hCD : 0 ≤ CD)
    (hr : 0 < r) (hrOne : r ≤ 1)
    (hell : ∀ s : ℝ, 1 ≤ s → 0 < ell s)
    (hellOne : ∀ s : ℝ, 1 ≤ s → ell s ≤ 1)
    (hc : ∀ s : ℝ, 1 ≤ s → |c s| ≤ 1)
    (htrap : ∀ s : ℝ, 1 ≤ s → ell s ≤ s ^ (-beta))
    (hXlow : ∀ s : ℝ, 1 ≤ s →
      actualHartreeSlowInnerRadius (ell s) ≤ a s * R)
    (hXup : ∀ s : ℝ, 1 ≤ s →
      a s * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hJet : ∀ s : ℝ, 1 ≤ s →
      ‖p s‖ + R * ‖q s‖ ≤ CD * s ^ (-rho))
    (hz : ∀ s : ℝ, 1 ≤ s → Measurable (z (time s)))
    (hHmeas : ∀ s : ℝ, 1 ≤ s → Measurable (H s))
    (hSup : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 0 < u →
      ‖z (time s) u‖ ≤ B)
    (hStrauss : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 1 ≤ u →
      u * ‖z (time s) u‖ ≤ A)
    (hHCorr : ∀ s : ℝ, 1 ≤ s → ∀ u : ℝ, 0 < u →
      ‖H s u‖ ≤ CH * bubble u)
    (hsep : ∀ s : ℝ, 1 ≤ s → 2 * r ≤ a s * R) :
    ∃ atom : WeightedResidualAtom ℂ,
      atom.value =
        actualHartreeMovingCorrectedKummerTruePDEResidualValue
          a ell c time R p q z H b omega r ∧
      atom.order = rho + actualHartreeLockedKappa beta rhoStar ∧
      atom.constant =
        2 * (4 * Real.pi * hartreeKappa) *
          actualKummerRepairCorrectedTimeConstant B A CH CX CD *
          (2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH) ^ 3 := by
  let k := actualHartreeLockedKappa beta rhoStar
  let M : ℝ :=
    2 + 9 * monopoleRadialBoundConstant + 2 * (B + A) + CH
  let Ct : ℝ := actualKummerRepairCorrectedTimeConstant B A CH CX CD
  let C0 : ℝ := 2 * (4 * Real.pi * hartreeKappa) * Ct * M ^ 3
  have hMono : 0 ≤ monopoleRadialBoundConstant :=
    monopoleRadialBoundConstant_pos.le
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hCt : 0 ≤ Ct := by
    dsimp [Ct, actualKummerRepairCorrectedTimeConstant]
    positivity
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    unfold hartreeKappa
    positivity
  let atom : WeightedResidualAtom ℂ :=
    { value := actualHartreeMovingCorrectedKummerTruePDEResidualValue
        a ell c time R p q z H b omega r
      order := rho + k
      constant := C0
      constant_nonneg := hC0
      bound := by
        intro s hs
        have hRaw :=
          actual_Hartree_moving_corrected_Kummer_full_PDE_next_locked_gain
            a ell c time R p q z H (b s) (omega s)
            s r B A CH beta rhoStar rho CX CD
            ha (haCont.continuousAt) hR
            (hell s hs) (hellOne s hs) (hc s hs) hB hA hCH
            hs hbeta hrhoStar hflat hrho (htrap s hs)
            (hXlow s hs) hCX (hXup s hs) hCD (hJet s hs)
            (hz s hs) (hHmeas s hs) (hSup s hs) (hStrauss s hs)
            (hHCorr s hs)
            hr hrOne (hsep s hs)
        dsimp only at hRaw
        simpa only
          [actualHartreeMovingCorrectedKummerTruePDEResidualValue,
            C0, M, Ct, k] using hRaw }
  refine ⟨atom, rfl, rfl, ?_⟩
  rfl

end HBL.TypeIIDynamicSelection
