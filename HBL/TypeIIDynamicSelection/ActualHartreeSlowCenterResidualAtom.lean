import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualWholeRadiationCenterReduction
import Mathlib.Tactic

/-!
# The genuine whole-radiation slow-center mismatch as a realized residual atom

The value is the actual Hartree center mismatch after the self-radiation
center and the real-linear mixed charge have been removed. Its time order
2*beta is proved by the strict quadratic mixed-center estimate.

No GainCause label or assigned order is used to prove the bound.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.ResidualLedger
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeSlowCenterResidualValue
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (s : ℝ) : ℝ :=
  actualRadiationCenter (Z s) -
    actualWholeRadiationInteractionCenterIncrement (V s) (Z s) +
    radialHartreeCenter (fun rho => 4 * (V s rho) ^ 3 * (Z s rho).re)

/-- The slow-center residual is a genuine weighted residual atom of order
2*beta = 1 + (2*beta-1).  All hypotheses are primitive spatial properties
of the same time-dependent physical profiles. -/
theorem actual_Hartree_slow_center_realized_atom
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (beta A CV CZ : ℝ)
    (hbeta : (1 / 2 : ℝ) < beta)
    (hA : 0 ≤ A) (hCV : 0 ≤ CV) (hCZ : 0 ≤ CZ)
    (hVmeas : ∀ s : ℝ, 1 ≤ s → Measurable (V s))
    (hZmeas : ∀ s : ℝ, 1 ≤ s → Measurable (Z s))
    (hV2 : ∀ s : ℝ, 1 ≤ s →
      IntegrableOn (fun rho => |V s rho| ^ 2) (Ioi (0 : ℝ)))
    (hZ2 : ∀ s : ℝ, 1 ≤ s →
      IntegrableOn (fun rho => ‖Z s rho‖ ^ 2) (Ioi (0 : ℝ)))
    (hVmass : ∀ s : ℝ, 1 ≤ s →
      (∫ rho in Ioi (0 : ℝ), |V s rho| ^ 2) ≤ CV)
    (hZmass : ∀ s : ℝ, 1 ≤ s →
      (∫ rho in Ioi (0 : ℝ), ‖Z s rho‖ ^ 2) ≤ CZ)
    (hZpoint : ∀ s : ℝ, 1 ≤ s → ∀ rho : ℝ, 0 < rho →
      ‖Z s rho‖ ≤ A * s ^ (-beta))
    (hFull : ∀ s : ℝ, 1 ≤ s →
      IntegrableOn
        (fun rho => ‖(V s rho : ℂ) + Z s rho‖ ^ 4)
        (Ioi (0 : ℝ)))
    (hV4 : ∀ s : ℝ, 1 ≤ s →
      IntegrableOn (fun rho => ‖(V s rho : ℂ)‖ ^ 4)
        (Ioi (0 : ℝ)))
    (hZ4 : ∀ s : ℝ, 1 ≤ s →
      IntegrableOn (fun rho => ‖Z s rho‖ ^ 4)
        (Ioi (0 : ℝ)))
    (hLinear : ∀ s : ℝ, 1 ≤ s →
      IntegrableOn
        (fun rho => 4 * (V s rho) ^ 3 * (Z s rho).re)
        (Ioi (0 : ℝ))) :
    ∃ atom : WeightedResidualAtom ℝ,
      atom.value = actualHartreeSlowCenterResidualValue V Z ∧
      atom.order = 2 * beta ∧
      atom.constant =
        4 * Real.pi * hartreeKappa * A ^ 2 * (8 * CV + 2 * CZ) := by
  let C : ℝ :=
    4 * Real.pi * hartreeKappa * A ^ 2 * (8 * CV + 2 * CZ)
  have hC : 0 ≤ C := by
    dsimp [C]
    unfold hartreeKappa
    positivity
  let atom : WeightedResidualAtom ℝ :=
    { value := actualHartreeSlowCenterResidualValue V Z
      order := 2 * beta
      constant := C
      constant_nonneg := hC
      bound := by
        intro s hs
        have h :=
          actual_whole_radiation_center_mismatch_twoBeta_gain
            (V s) (Z s) hs hbeta
            (hVmeas s hs) (hZmeas s hs)
            (hV2 s hs) (hZ2 s hs)
            (hVmass s hs) (hZmass s hs)
            (hZpoint s hs)
            (hFull s hs) (hV4 s hs) (hZ4 s hs) (hLinear s hs)
        rw [Real.norm_eq_abs]
        simpa only [actualHartreeSlowCenterResidualValue, C] using h.2 }
  refine ⟨atom, rfl, rfl, ?_⟩
  rfl

theorem actual_Hartree_slow_center_realized_gain_positive
    (beta : ℝ) (hbeta : (1 / 2 : ℝ) < beta) :
    1 < 2 * beta := by
  linarith

end HBL.TypeIIDynamicSelection
