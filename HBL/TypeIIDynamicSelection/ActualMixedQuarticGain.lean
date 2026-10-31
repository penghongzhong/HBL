import HBL.TypeIIDynamicSelection.ActualWholeRadiationSelfCubic
import HBL.HartreePhysicalLinearization
import Mathlib.Tactic

/-!
# Genuine quadratic gain from the whole-radiation Hartree mixed quartic

The exact density |V+Z|^4 - |V|^4 - |Z|^4 contains a real-linear term
4 V^3 Re Z and a remainder at least quadratic in Z.  The derivation uses
the physical complex norm, not an abstract generating-series label.

Under a *stated* bound ‖Z(s,r)‖ ≤ A s^{-beta}, beta > 1/2, the nonlinear
mixed-density remainder is bounded at order s^{-2 beta}.  Its positive
excess over s^{-1} is 2 beta - 1.  The decay input must ultimately be
proved for an actual Hartree profile before manuscript environment
prop:one-layer-stage3 can be counted as closed.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- The genuinely quadratic and cubic part of the whole-radiation
Hartree density after removing the true real-linear source. -/
def actualWholeRadiationMixedHigher
    (V : ℝ → ℝ) (Z : ℝ → ℂ) (rho : ℝ) : ℝ :=
  2 * (V rho) ^ 2 * ‖Z rho‖ ^ 2 +
    4 * (V rho) ^ 2 * (Z rho).re ^ 2 +
      4 * V rho * (Z rho).re * ‖Z rho‖ ^ 2

/-- Exact expansion of the SAME physical quartic density, without a
support restriction and without an input terminal blowup rate. -/
theorem actual_whole_radiation_mixed_linear_higher_exact
    (V : ℝ → ℝ) (Z : ℝ → ℂ) (rho : ℝ) :
    actualWholeRadiationMixedQuartic V Z rho =
      4 * V rho ^ 3 * (Z rho).re +
        actualWholeRadiationMixedHigher V Z rho := by
  have hnorm :=
    HBL.RegularRadiation.PhysicalExpansion.norm_sq_real_add (V rho) (Z rho)
  have hbase : ‖(V rho : ℂ)‖ ^ 2 = (V rho) ^ 2 := by
    simp [Complex.norm_real, sq_abs]
  unfold actualWholeRadiationMixedQuartic actualWholeRadiationMixedHigher
  calc
    ‖(V rho : ℂ) + Z rho‖ ^ 4 -
          ‖(V rho : ℂ)‖ ^ 4 - ‖Z rho‖ ^ 4 =
        (‖(V rho : ℂ) + Z rho‖ ^ 2) ^ 2 -
          (‖(V rho : ℂ)‖ ^ 2) ^ 2 -
            (‖Z rho‖ ^ 2) ^ 2 := by ring
    _ = _ := by
      rw [hnorm, hbase]
      ring

/-- Quantitative second-order bound for all quadratic/cubic
bubble-radiation density interactions. -/
theorem actual_whole_radiation_mixed_higher_abs_le
    (V : ℝ → ℝ) (Z : ℝ → ℂ) (rho : ℝ) :
    |actualWholeRadiationMixedHigher V Z rho| ≤
      (6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖) *
        ‖Z rho‖ ^ 2 := by
  let a : ℝ := V rho
  let x : ℝ := (Z rho).re
  let z : ℝ := ‖Z rho‖
  have hz : 0 ≤ z := norm_nonneg _
  have hre : |x| ≤ z := Complex.abs_re_le_norm _
  have hx2 : x ^ 2 ≤ z ^ 2 := by
    calc
      x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ z ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hre 2
  have hcross : |4 * a * x * z ^ 2| ≤ 4 * |a| * z ^ 3 := by
    calc
      |4 * a * x * z ^ 2| = 4 * |a| * |x| * z ^ 2 := by
        simp only [abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num),
          abs_of_nonneg (sq_nonneg z)]
      _ ≤ 4 * |a| * z * z ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hre (by positivity)) (sq_nonneg z)
      _ = 4 * |a| * z ^ 3 := by ring
  have hbase : 0 ≤ 2 * a ^ 2 * z ^ 2 + 4 * a ^ 2 * x ^ 2 := by
    positivity
  have hquad : 4 * a ^ 2 * x ^ 2 ≤ 4 * a ^ 2 * z ^ 2 :=
    mul_le_mul_of_nonneg_left hx2 (by positivity)
  change
    |(2 * a ^ 2 * z ^ 2 + 4 * a ^ 2 * x ^ 2) +
      4 * a * x * z ^ 2| ≤
        (6 * |a| ^ 2 + 4 * |a| * z) * z ^ 2
  have htri := abs_add_le (2 * a ^ 2 * z ^ 2 + 4 * a ^ 2 * x ^ 2)
    (4 * a * x * z ^ 2)
  rw [abs_of_nonneg hbase] at htri
  calc
    _ ≤ 2 * a ^ 2 * z ^ 2 + 4 * a ^ 2 * x ^ 2 +
        |4 * a * x * z ^ 2| := htri
    _ ≤ 2 * a ^ 2 * z ^ 2 + 4 * a ^ 2 * x ^ 2 +
        4 * |a| * z ^ 3 := by linarith only [hcross]
    _ ≤ (6 * |a| ^ 2 + 4 * |a| * z) * z ^ 2 := by
      rw [sq_abs]
      nlinarith only [hquad]

/-- A genuine positive-order gain of the mixed Hartree nonlinear
density, *conditional only on the explicitly displayed primitive
physical amplitude and decay estimates*.  No \`GeneratedTerm.order\`
is defined to make the conclusion tautological. -/
theorem actual_whole_radiation_mixed_higher_twoBeta_gain
    (V : ℝ → ℝ) (Z : ℝ → ℂ) (rho : ℝ)
    {s beta M A : ℝ}
    (hs : 1 ≤ s) (hbeta : (1 / 2 : ℝ) < beta)
    (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hV : |V rho| ≤ M)
    (hZ : ‖Z rho‖ ≤ A * s ^ (-beta)) :
    0 < 2 * beta - 1 ∧
      |actualWholeRadiationMixedHigher V Z rho| ≤
        (6 * M ^ 2 * A ^ 2 + 4 * M * A ^ 3) *
          s ^ (-2 * beta) := by
  have hgain : 0 < 2 * beta - 1 := by linarith
  have hpow : s ^ (-beta) ≤ 1 := by
    have hle : -beta ≤ (0 : ℝ) := by linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hs hle
  have hZ0 : ‖Z rho‖ ≤ A := by
    calc
      ‖Z rho‖ ≤ A * s ^ (-beta) := hZ
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hpow hA
      _ = A := by ring
  have hV2 : |V rho| ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hV 2
  have hprod : |V rho| * ‖Z rho‖ ≤ M * A :=
    mul_le_mul hV hZ0 (norm_nonneg _) hM
  have hcoeff :
      6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖ ≤
        6 * M ^ 2 + 4 * M * A := by
    nlinarith only [hV2, hprod]
  have hrpow : (s ^ (-beta)) ^ 2 = s ^ (-2 * beta) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ s) (-beta) 2]
    congr 1
    ring
  have hZ2 : ‖Z rho‖ ^ 2 ≤ A ^ 2 * s ^ (-2 * beta) := by
    calc
      ‖Z rho‖ ^ 2 ≤ (A * s ^ (-beta)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hZ 2
      _ = A ^ 2 * s ^ (-2 * beta) := by rw [mul_pow, hrpow]
  refine ⟨hgain, ?_⟩
  calc
    _ ≤ (6 * |V rho| ^ 2 + 4 * |V rho| * ‖Z rho‖) *
          ‖Z rho‖ ^ 2 :=
      actual_whole_radiation_mixed_higher_abs_le V Z rho
    _ ≤ (6 * M ^ 2 + 4 * M * A) *
          (A ^ 2 * s ^ (-2 * beta)) :=
      mul_le_mul hcoeff hZ2 (sq_nonneg _) (by positivity)
    _ = (6 * M ^ 2 * A ^ 2 + 4 * M * A ^ 3) *
          s ^ (-2 * beta) := by ring

end HBL.TypeIIDynamicSelection
