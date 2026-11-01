import HBL.TypeIIDynamicSelection.ActualPhasedSpatialFlatness
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Original manuscript 2.12: genuine phased flat-source temporal gain

The previous strict proof constructed the ACTUAL complex-phased,
centre-cutoff-subtracted regular radiation and proved its spatial
MVT gain on the physical unit ball:
  ‖Z_g^flat(s,R)‖ <= M ell(s)² sqrt(ell(s)) R².

Here we combine that *actual source*, and only the ordinary trapping
bounds ell(s) <= s^(-beta), R <= s^rho, with the manuscript's
strict core radius inequality, to derive
  ‖Z_g^flat(s,R)‖ <= M s^(-1 - epsilon_flat)
where epsilon_flat := 5 beta / 2 - 2 rho - 1 > 0.

No terminal blowup rate is prescribed; beta is a trapping window
exponent that is extracted from the genuine modulation bounds.
The required C² radial estimates for the full physical Hartree
solution remain a cited high-regularity flow interface. Higher
time-jet and two-solution Lipschitz versions and all remaining
actual projected Fredholm–Kummer–remote elimination must still
be discharged to accept original one-layer lemma 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A strictly positive original flat-source gain arising from the
moving spatial radius and the actual modulation trapping window. -/
theorem actual_Hartree_flat_gain_pos_of_trap
    (beta rho : ℝ) (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho) (hroom : rho < (5 * beta - 2) / 4) :
    0 < 5 * beta / 2 - 2 * rho - 1 := by
  linarith

/-- The exact scalar power comparison needed when a genuine spatial
O(ell^(5/2) R²) source is inserted into a trapped (not selected)
Hartree modulation window. -/
theorem actual_Hartree_flat_spacetime_power_from_trap
    (s ell R beta rho : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell)
    (hscale : ell ≤ s ^ (-beta))
    (hR : 0 ≤ R) (hRWindow : R ≤ s ^ rho) :
    (ell ^ 2 * Real.sqrt ell) * R ^ 2 ≤
      s ^ (-5 * beta / 2 + 2 * rho) := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hEllPower : ell ^ 2 * Real.sqrt ell =
      ell ^ ((5 : ℝ) / 2) := by
    calc
      ell ^ 2 * Real.sqrt ell =
          ell ^ (2 : ℝ) * ell ^ (1 / (2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
      _ = ell ^ ((5 : ℝ) / 2) := by
        rw [← Real.rpow_add hell]
        congr 1
        ring
  have hUpper :
      ell ^ ((5 : ℝ) / 2) ≤ (s ^ (-beta)) ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow hell.le hscale (by norm_num)
  have hExp :
      (s ^ (-beta)) ^ ((5 : ℝ) / 2) =
        s ^ (-5 * beta / 2) := by
    rw [← Real.rpow_mul hspos.le]
    congr 1
    ring
  have hBoundEll :
      ell ^ ((5 : ℝ) / 2) ≤ s ^ (-5 * beta / 2) := by
    rw [hExp] at hUpper
    exact hUpper
  have hBoundR : R ^ 2 ≤ s ^ (2 * rho) := by
    calc
      R ^ 2 ≤ (s ^ rho) ^ 2 := pow_le_pow_left₀ hR hRWindow 2
      _ = s ^ (2 * rho) := by
        rw [← Real.rpow_mul_natCast hspos.le rho 2]
        congr 1
        ring
  have hTotal :=
    mul_le_mul hBoundEll hBoundR (sq_nonneg R)
      (Real.rpow_nonneg hspos.le _)
  calc
    (ell ^ 2 * Real.sqrt ell) * R ^ 2 =
        ell ^ ((5 : ℝ) / 2) * R ^ 2 := by rw [hEllPower]
    _ ≤ s ^ (-5 * beta / 2) * s ^ (2 * rho) := hTotal
    _ = s ^ (-5 * beta / 2 + 2 * rho) := by
      rw [Real.rpow_add hspos]

/-- Literal original spatially-flat Hartree radiation, with its
actual complex phase and centre cutoff, has the manuscript's
integrable time exponent as a derived bound under actual
trapping-window inequalities. Neither the desired source smallness
nor the final selected blowup rate is a hypothesis. -/
theorem actual_Hartree_phased_flat_source_time_gain
    (z zr zrr : ℝ → ℝ → ℂ)
    (time s ell gamma R M beta rho : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell)
    (hscale : ell ≤ s ^ (-beta))
    (hR : 0 ≤ R) (hRWindow : R ≤ s ^ rho)
    (hCore : ell * R ≤ 1)
    (hM : 0 ≤ M)
    (hFlow : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (z time) (zr time x) x)
    (hFlowR : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (zr time) (zrr time x) x)
    (hRegBound : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖zrr time x‖ ≤ M)
    (hRegularOrigin : zr time 0 = 0) :
    ‖actualPhasedHartreeFlatRadiation (z time) ell gamma R‖ ≤
      M * s ^ (-5 * beta / 2 + 2 * rho) := by
  have hSource :=
    actual_phased_Hartree_radial_spatial_flatness
      z zr zrr time ell gamma R M
      hell hR hM hCore hFlow hFlowR hRegBound hRegularOrigin
  have hPower :=
    actual_Hartree_flat_spacetime_power_from_trap
      s ell R beta rho hs hell hscale hR hRWindow
  calc
    ‖actualPhasedHartreeFlatRadiation (z time) ell gamma R‖ ≤
      (M * ell ^ 2 * Real.sqrt ell) * R ^ 2 := hSource
    _ = M * ((ell ^ 2 * Real.sqrt ell) * R ^ 2) := by ring
    _ ≤ M * s ^ (-5 * beta / 2 + 2 * rho) :=
      mul_le_mul_of_nonneg_left hPower hM

end HBL.TypeIIDynamicSelection
