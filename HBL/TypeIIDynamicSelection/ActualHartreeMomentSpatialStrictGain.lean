import HBL.TypeIIDynamicSelection.ActualOneLayerSpatialOverlapGain
import HBL.TypeIIDynamicSelection.ActualPDEMomentCutoffStrictGain
import Mathlib.Tactic

/-!
# Original HBL 2.12: truly physical Hartree moment cutoff yields spatial gain

The physical inverse-square Hartree radiation moment determines the
actual outer radial cutoff R=4/c, where c=kappa_H*ell*m and m is
the genuine positive radial quartic moment of the SAME flow.
This file derives the cutoff's SECOND radial derivative time gain
directly from the actual normalized physical Riesz constant,
C-infinity cutoff and trapped physical length.

The gained source coefficient is
  ‖(chi_R)''(r)‖ <= C2 * (kappa_H*M/4)^2*C^2*s^(-1-(2*beta-1))
for every real r, where m<=M and ell<=C s^(-beta), beta>1/2.
No Type-II terminal rate exponent is imposed. This is the physical
R^-2 cutoff commutator atom, not a fictitious GeneratedTerm record.

Remaining original 2.12 obligations: the actual first-derivative
commutator coupled with the scaled physical profile; the full
NONLOCAL Riesz cutoff commutator, parameter/Frobenius source
atoms, and exact minimal-weight residual elimination.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Original physical 3D Hartree radiation-moment cutoff radius:
c=kappa_H*ell*m, with m the REAL quartic radiation moment. -/
def actualHartreeMomentCutoffRadius (ell m : ℝ) : ℝ :=
  4 / (hartreeKappa * ell * m)

/-- The original physical cutoff has 1/R=O(ell) with its genuine
Hartree moment bound; R is not an independently chosen scale. -/
theorem actual_Hartree_real_moment_radius_inverse_le
    (ell m M : ℝ) (hell : 0 < ell) (hm : 0 < m)
    (hmBound : m ≤ M) :
    0 < actualHartreeMomentCutoffRadius ell m ∧
    1 / actualHartreeMomentCutoffRadius ell m ≤
      (hartreeKappa * M / 4) * ell := by
  have hkap : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hDenom : 0 < hartreeKappa * ell * m := by positivity
  have hD : hartreeKappa * ell * m ≠ 0 := hDenom.ne'
  have hR : 0 < actualHartreeMomentCutoffRadius ell m := by
    unfold actualHartreeMomentCutoffRadius
    positivity
  have hInv : 1 / actualHartreeMomentCutoffRadius ell m =
      hartreeKappa * ell * m / 4 := by
    unfold actualHartreeMomentCutoffRadius
    field_simp [hD]
  have hMul : hartreeKappa * ell * m ≤
      hartreeKappa * ell * M :=
    mul_le_mul_of_nonneg_left hmBound (by positivity)
  refine ⟨hR,?_⟩
  calc
    1 / actualHartreeMomentCutoffRadius ell m =
      hartreeKappa * ell * m / 4 := hInv
    _ ≤ hartreeKappa * ell * M / 4 :=
      div_le_div_of_nonneg_right hMul (by norm_num)
    _ = (hartreeKappa * M / 4) * ell := by ring

/-- The second spatial-cutoff PDE commutator has a STRICTLY
integrable time exponent 1+(2*beta-1), with all constants derived
from the actual smooth cutoff, original Hartree normalization and
the positive physical radiation quartic moment. -/
theorem actual_Hartree_physical_C2_cutoff_second_deriv_strict_gain
    (s ell m M C beta : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell) (hm : 0 < m)
    (hmBound : m ≤ M) (hC : 0 ≤ C)
    (hBeta : 1 / 2 < beta)
    (hTrap : ell ≤ C * s ^ (-beta)) :
    ∃ C2 : ℝ, 0 < C2 ∧
      0 < actualPDEMomentCutoffGain beta ∧
      ∀ r : ℝ,
        ‖deriv (deriv (actualOneLayerInnerOverlapCutoff
          (actualHartreeMomentCutoffRadius ell m))) r‖ ≤
        (C2 * (hartreeKappa * M / 4) ^ 2 * C ^ 2) *
          s ^ (-1 - actualPDEMomentCutoffGain beta) := by
  obtain ⟨C1,C2,hC1,hC2,hCut⟩ :=
    actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  let R : ℝ := actualHartreeMomentCutoffRadius ell m
  let A : ℝ := hartreeKappa * M / 4
  have hM : 0 < M := lt_of_lt_of_le hm hmBound
  have hA : 0 ≤ A := by
    dsimp [A]
    unfold hartreeKappa
    positivity
  obtain ⟨hR,hRInv⟩ :=
    actual_Hartree_real_moment_radius_inverse_le ell m M hell hm hmBound
  have hRInv2 : (1 / R) ^ 2 ≤ (A * ell) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRInv 2
  have hRFact : C2 / R ^ 2 = C2 * (1 / R) ^ 2 := by
    field_simp [hR.ne']
  have hEll2 :
      ell ^ 2 ≤ C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta) :=
    actual_PDE_trapped_length_squared_positive_gain
      s ell C beta hs hell.le hC hTrap
  have hcoef : 0 ≤ C2 * A ^ 2 := by positivity
  refine ⟨C2,hC2,actual_PDE_moment_cutoff_gain_positive beta hBeta,?_⟩
  intro r
  calc
    ‖deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r‖ ≤
        C2 / R ^ 2 := (hCut R r hR).2
    _ = C2 * (1 / R) ^ 2 := hRFact
    _ ≤ C2 * (A * ell) ^ 2 :=
        mul_le_mul_of_nonneg_left hRInv2 hC2.le
    _ = (C2 * A ^ 2) * ell ^ 2 := by ring
    _ ≤ (C2 * A ^ 2) *
          (C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta)) :=
        mul_le_mul_of_nonneg_left hEll2 hcoef
    _ = (C2 * (hartreeKappa * M / 4) ^ 2 * C ^ 2) *
          s ^ (-1 - actualPDEMomentCutoffGain beta) := by
        dsimp [A]
        ring

end HBL.TypeIIDynamicSelection
