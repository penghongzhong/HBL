import HBL.TypeIIDynamicSelection.ActualHartreeComplexCorrectionResidual
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalOneLayerGain
import Mathlib.Tactic

/-!
# Actual Hartree Taylor remainder has the physical next-layer gain

The exact correction-residual identity leaves a genuine nonlinear Taylor
remainder.  This file proves directly from the existing Hartree Taylor bound
that a correction of order s^(-rho) produces a quadratic remainder of order
s^(-2 rho), and therefore at least one physical profile gain above rho once
rho >= actualHartreePhysicalKappa.

No generated-order label is used to prove the estimate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_correction_Taylor_quadratic_time_order
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ)
    (rho M CH : ℝ)
    (hs : 1 ≤ s) (hrho : 0 ≤ rho)
    (hM : 0 ≤ M) (hCH : 0 ≤ CH)
    (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ (CH * s ^ (-rho)) * bubble x) :
    ‖complexRadialRenormalizedResidual
        (fun t x => U t x + H t x) (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual U b omega s r -
      actualHartreeComplexCorrectionLinearPart
        U H b omega db domega s r‖ ≤
      (63 * (M + CH) ^ 5 * CH ^ 2) *
        s ^ (-2 * rho) * bubble r ^ 5 := by
  let e : ℝ := CH * s ^ (-rho)
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hsPow0 : 0 ≤ s ^ (-rho) := Real.rpow_nonneg hs0 _
  have he : 0 ≤ e := mul_nonneg hCH hsPow0
  have hsPowOne : s ^ (-rho) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have heCH : e ≤ CH := by
    dsimp [e]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsPowOne hCH
  have hraw := actual_Hartree_complex_correction_residual_quadratic
    U H b omega db domega s r hr hUtime hHtime
      hUspace hHspace hUsecond hHsecond hUmeas hHmeas
      M e hM he hUB (by simpa only [e] using hHB)
  have hsum : M + e ≤ M + CH := add_le_add_left heCH M |> by simpa [add_comm]
  have hsum0 : 0 ≤ M + e := add_nonneg hM he
  have hsumPow : (M + e) ^ 5 ≤ (M + CH) ^ 5 :=
    pow_le_pow_left₀ hsum0 hsum 5
  have he2 : e ^ 2 = CH ^ 2 * s ^ (-2 * rho) := by
    dsimp [e]
    rw [mul_pow]
    have hp :
        (s ^ (-rho)) ^ 2 = s ^ (-2 * rho) := by
      rw [← Real.rpow_mul_natCast hs0 (-rho) 2]
      congr 1
      ring
    rw [hp]
  have hb5 : 0 ≤ bubble r ^ 5 :=
    pow_nonneg (bubble_nonneg r) 5
  have hcoef : 0 ≤ 63 * (M + CH) ^ 5 := by positivity
  calc
    _ ≤ 63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 := hraw
    _ ≤ 63 * (M + CH) ^ 5 * e ^ 2 * bubble r ^ 5 := by
      gcongr
    _ = (63 * (M + CH) ^ 5 * CH ^ 2) *
        s ^ (-2 * rho) * bubble r ^ 5 := by rw [he2]; ring

theorem actual_Hartree_correction_Taylor_next_physical_layer
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ)
    (beta rhoStar rho M CH : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hs : 1 ≤ s)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hM : 0 ≤ M) (hCH : 0 ≤ CH)
    (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ (CH * s ^ (-rho)) * bubble x) :
    ‖complexRadialRenormalizedResidual
        (fun t x => U t x + H t x) (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual U b omega s r -
      actualHartreeComplexCorrectionLinearPart
        U H b omega db domega s r‖ ≤
      (63 * (M + CH) ^ 5 * CH ^ 2) *
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) *
        bubble r ^ 5 := by
  have hkpos := actual_Hartree_physical_kappa_positive
    beta rhoStar hbeta hrhoStar hflat
  have hrho0 : 0 ≤ rho := le_trans hkpos.le hrho
  have hraw := actual_Hartree_correction_Taylor_quadratic_time_order
    U H b omega db domega s r rho M CH hs hrho0 hM hCH hr
    hUtime hHtime hUspace hHspace hUsecond hHsecond
    hUmeas hHmeas hUB hHB
  have hexp : -2 * rho ≤
      -(rho + actualHartreePhysicalKappa beta rhoStar) := by
    linarith
  have hp : s ^ (-2 * rho) ≤
      s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) :=
    Real.rpow_le_rpow_of_exponent_le hs hexp
  have hc : 0 ≤ 63 * (M + CH) ^ 5 * CH ^ 2 := by positivity
  have hb : 0 ≤ bubble r ^ 5 := pow_nonneg (bubble_nonneg r) 5
  calc
    _ ≤ (63 * (M + CH) ^ 5 * CH ^ 2) *
        s ^ (-2 * rho) * bubble r ^ 5 := hraw
    _ ≤ (63 * (M + CH) ^ 5 * CH ^ 2) *
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) *
        bubble r ^ 5 := by
      gcongr

end HBL.TypeIIDynamicSelection
