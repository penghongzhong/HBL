import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualPhasedFlatTimeWeight
import HBL.TypeIIDynamicSelection.ActualFlatGainIntegrability
import Mathlib.Tactic

/-!
# The genuine spatially-flat radiation source as a realized residual atom

The value is the actual phased Hartree flat-radiation source along one
time-dependent physical radiation flow. Its order is obtained from the
proved spatial flatness estimate and the moving-core trap.

No structural GainCause or assigned order is used.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.ResidualLedger

def actualHartreeFlatResidualValue
    (z : ℝ → ℝ → ℂ)
    (time ell gamma R : ℝ → ℝ) (s : ℝ) : ℂ :=
  actualPhasedHartreeFlatRadiation
    (z (time s)) (ell s) (gamma s) (R s)

/-- The physical flat-radiation source is a realized complex residual atom
of order 1+epsilon_flat. -/
theorem actual_Hartree_flat_radiation_realized_atom
    (z zr zrr : ℝ → ℝ → ℂ)
    (time ell gamma R : ℝ → ℝ)
    (M beta rho : ℝ)
    (hM : 0 ≤ M)
    (_hbeta : 1 / 2 < beta)
    (_hrho : 0 < rho)
    (_hflat : rho < (5 * beta - 2) / 4)
    (hell : ∀ s : ℝ, 1 ≤ s → 0 < ell s)
    (hscale : ∀ s : ℝ, 1 ≤ s → ell s ≤ s ^ (-beta))
    (hR : ∀ s : ℝ, 1 ≤ s → 0 ≤ R s)
    (hRWindow : ∀ s : ℝ, 1 ≤ s → R s ≤ s ^ rho)
    (hCore : ∀ s : ℝ, 1 ≤ s → ell s * R s ≤ 1)
    (hFlow : ∀ s : ℝ, 1 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (z (time s)) (zr (time s) x) x)
    (hFlowR : ∀ s : ℝ, 1 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (zr (time s)) (zrr (time s) x) x)
    (hRegBound : ∀ s : ℝ, 1 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      ‖zrr (time s) x‖ ≤ M)
    (hRegularOrigin : ∀ s : ℝ, 1 ≤ s → zr (time s) 0 = 0) :
    ∃ atom : WeightedResidualAtom ℂ,
      atom.value = actualHartreeFlatResidualValue z time ell gamma R ∧
      atom.order = 1 + actualHartreeFlatGain beta rho ∧
      atom.constant = M := by
  let atom : WeightedResidualAtom ℂ :=
    { value := actualHartreeFlatResidualValue z time ell gamma R
      order := 1 + actualHartreeFlatGain beta rho
      constant := M
      constant_nonneg := hM
      bound := by
        intro s hs
        have h :=
          actual_Hartree_phased_flat_source_time_gain
            z zr zrr (time s) s (ell s) (gamma s) (R s)
            M beta rho hs (hell s hs) (hscale s hs)
            (hR s hs) (hRWindow s hs) (hCore s hs) hM
            (hFlow s hs) (hFlowR s hs) (hRegBound s hs)
            (hRegularOrigin s hs)
        rw [actual_Hartree_flat_power_exact beta rho] at h
        have hexp :
            -1 - actualHartreeFlatGain beta rho =
              -(1 + actualHartreeFlatGain beta rho) := by ring
        rw [hexp] at h
        simpa only [actualHartreeFlatResidualValue] using h }
  exact ⟨atom, rfl, rfl, rfl⟩

theorem actual_Hartree_flat_radiation_realized_gain_positive
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4) :
    1 < 1 + actualHartreeFlatGain beta rho := by
  have h := actual_Hartree_flat_gain_strict_pos beta rho hbeta hrho hflat
  linarith

end HBL.TypeIIDynamicSelection
