import HBL.TypeIIDynamicSelection.ActualKummerInterfaceRepair
import Mathlib.Tactic

/-!
# Genuine source-jet C² repair at the original Kummer outer interface

The old affine source-dependent repair is C¹ but has an unaccounted
second-derivative jump, -w''(B)/a², at the actual interface aB.
Here the extra curvature j is not introduced as independent physical
source data: it is precisely intended to be w''(B) from the same
original nonlocal Hartree Kummer Green field.

The theorem proves endpoint C² jets of the concrete, already available
smooth overlap cutoff times the source-dependent quadratic Taylor
polynomial. It does not construct w'', prove the inner Fredholm C²
join, or bound the nonlinear PDE residual/time derivative.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeC2RepairPolynomial
    (B : ℝ) (p q j : ℂ) (r : ℝ) : ℂ :=
  p + ((r - B : ℝ) : ℂ) * q +
    (((r - B : ℝ) : ℂ) ^ 2) * j / 2

def actualHartreeC2SourceJetRepair
    (B : ℝ) (p q j : ℂ) (r : ℝ) : ℂ :=
  actualKummerRepairCutoff B r *
    actualHartreeC2RepairPolynomial B p q j r

theorem actual_Hartree_C2_repair_polynomial_hasDerivAt
    (B r : ℝ) (p q j : ℂ) :
    HasDerivAt (actualHartreeC2RepairPolynomial B p q j)
      (q + ((r - B : ℝ) : ℂ) * j) r := by
  have hb : HasDerivAt (fun x : ℝ => ((x - B : ℝ) : ℂ)) 1 r := by
    simpa using ((hasDerivAt_id r).sub_const B).ofReal_comp
  have hlin : HasDerivAt (fun x : ℝ => ((x - B : ℝ) : ℂ) * q) q r := by
    simpa using hb.mul_const q
  have hquad :
      HasDerivAt
        (fun x : ℝ => (((x - B : ℝ) : ℂ) ^ 2) * j / 2)
        (((r - B : ℝ) : ℂ) * j) r := by
    convert (hb.pow 2).mul_const (j / 2) using 1
    · ext x
      simp only [Pi.pow_apply]
      push_cast
      ring
    · norm_num
  convert ((hlin.add hquad).const_add p) using 1
  ext x
  simp only [Pi.add_apply]
  unfold actualHartreeC2RepairPolynomial
  push_cast
  ring

theorem actual_Hartree_C2_repair_polynomial_second_hasDerivAt
    (B r : ℝ) (p q j : ℂ) :
    HasDerivAt (deriv (actualHartreeC2RepairPolynomial B p q j))
      j r := by
  have hb : HasDerivAt (fun x : ℝ => ((x - B : ℝ) : ℂ)) 1 r := by
    simpa using ((hasDerivAt_id r).sub_const B).ofReal_comp
  have hDeriv :
      deriv (actualHartreeC2RepairPolynomial B p q j) =
        (fun x : ℝ => q + ((x - B : ℝ) : ℂ) * j) := by
    funext x
    exact (actual_Hartree_C2_repair_polynomial_hasDerivAt B x p q j).deriv
  rw [hDeriv]
  simpa using (hb.mul_const j).const_add q

/-- The actual pre-existing smooth cutoff, not a hypothetical cutoff,
is constant one left and constant zero right on the needed open sets. -/
private theorem actual_Hartree_C2_repair_cutoff_one_left
    (B x : ℝ) (hB : 0 < B) (hx : x < B + B / 3) :
    actualKummerRepairCutoff B x = 1 := by
  have hc : cutoff ((x - B) / (B / 3)) = 0 :=
    cutoff_zero_of_le_one _ ((div_le_one (by positivity)).2 (by linarith))
  simp [actualKummerRepairCutoff, actualOneLayerInnerOverlapCutoff, hc]

private theorem actual_Hartree_C2_repair_cutoff_zero_right
    (B x : ℝ) (hB : 0 < B) (hx : B + 2 * (B / 3) < x) :
    actualKummerRepairCutoff B x = 0 := by
  have hc : cutoff ((x - B) / (B / 3)) = 1 :=
    cutoff_one_of_two_le _ ((le_div_iff₀ (by positivity)).2 (by linarith))
  simp [actualKummerRepairCutoff, actualOneLayerInnerOverlapCutoff, hc]

/-- Genuine value, slope AND curvature at the actual two outer endpoints.
This is a strictly auxiliary analytic regularity interface, not §2.13. -/
theorem actual_Hartree_C2_source_jet_repair_endpoint_jets
    (B : ℝ) (hB : 0 < B) (p q j : ℂ) :
    actualHartreeC2SourceJetRepair B p q j B = p ∧
    deriv (actualHartreeC2SourceJetRepair B p q j) B = q ∧
    deriv (deriv (actualHartreeC2SourceJetRepair B p q j)) B = j ∧
    actualHartreeC2SourceJetRepair B p q j (2 * B) = 0 ∧
    deriv (actualHartreeC2SourceJetRepair B p q j) (2 * B) = 0 ∧
    deriv (deriv (actualHartreeC2SourceJetRepair B p q j)) (2 * B) = 0 := by
  have hLeftBound : B < B + B / 3 := by linarith
  have hRightBound : B + 2 * (B / 3) < 2 * B := by linarith
  have hNearLeft :
      actualHartreeC2SourceJetRepair B p q j =ᶠ[𝓝 B]
        actualHartreeC2RepairPolynomial B p q j := by
    filter_upwards [Iio_mem_nhds hLeftBound] with x hx
    change actualKummerRepairCutoff B x *
        actualHartreeC2RepairPolynomial B p q j x =
      actualHartreeC2RepairPolynomial B p q j x
    rw [actual_Hartree_C2_repair_cutoff_one_left B x hB hx]
    ring
  have hNearRight :
      actualHartreeC2SourceJetRepair B p q j =ᶠ[𝓝 (2 * B)]
        (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hRightBound] with x hx
    change actualKummerRepairCutoff B x *
        actualHartreeC2RepairPolynomial B p q j x = 0
    rw [actual_Hartree_C2_repair_cutoff_zero_right B x hB hx]
    ring
  have hDerivNearLeft :
      deriv (actualHartreeC2SourceJetRepair B p q j) =ᶠ[𝓝 B]
        deriv (actualHartreeC2RepairPolynomial B p q j) := by
    filter_upwards [Iio_mem_nhds hLeftBound] with x hx
    have hLocal :
        actualHartreeC2SourceJetRepair B p q j =ᶠ[𝓝 x]
          actualHartreeC2RepairPolynomial B p q j := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change actualKummerRepairCutoff B y *
          actualHartreeC2RepairPolynomial B p q j y =
        actualHartreeC2RepairPolynomial B p q j y
      rw [actual_Hartree_C2_repair_cutoff_one_left B y hB hy]
      ring
    exact hLocal.deriv_eq
  have hDerivNearRight :
      deriv (actualHartreeC2SourceJetRepair B p q j) =ᶠ[𝓝 (2 * B)]
        (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hRightBound] with x hx
    have hLocal :
        actualHartreeC2SourceJetRepair B p q j =ᶠ[𝓝 x]
          (fun _ => (0 : ℂ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change actualKummerRepairCutoff B y *
          actualHartreeC2RepairPolynomial B p q j y = 0
      rw [actual_Hartree_C2_repair_cutoff_zero_right B y hB hy]
      ring
    rw [hLocal.deriv_eq]
    exact deriv_const x (0 : ℂ)
  have hLeftFirst :
      HasDerivAt (actualHartreeC2SourceJetRepair B p q j) q B := by
    have hp := actual_Hartree_C2_repair_polynomial_hasDerivAt B B p q j
    have hpq : q + ((B - B : ℝ) : ℂ) * j = q := by simp
    rw [hpq] at hp
    exact hp.congr_of_eventuallyEq hNearLeft
  have hLeftSecond :
      HasDerivAt (deriv (actualHartreeC2SourceJetRepair B p q j))
        j B :=
    (actual_Hartree_C2_repair_polynomial_second_hasDerivAt B B p q j).congr_of_eventuallyEq
      hDerivNearLeft
  have hRightFirst :
      HasDerivAt (actualHartreeC2SourceJetRepair B p q j) 0 (2 * B) :=
    (hasDerivAt_const (2 * B) (0 : ℂ)).congr_of_eventuallyEq hNearRight
  have hRightSecond :
      HasDerivAt (deriv (actualHartreeC2SourceJetRepair B p q j))
        0 (2 * B) :=
    (hasDerivAt_const (2 * B) (0 : ℂ)).congr_of_eventuallyEq hDerivNearRight
  refine ⟨?_, hLeftFirst.deriv, hLeftSecond.deriv, ?_,
    hRightFirst.deriv, hRightSecond.deriv⟩
  · rw [hNearLeft.eq_of_nhds]
    simp [actualHartreeC2RepairPolynomial]
  · exact hNearRight.eq_of_nhds

end HBL.TypeIIDynamicSelection
