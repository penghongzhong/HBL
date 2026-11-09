import HBL.TypeIIDynamicSelection.ActualHartreeOneGlobalCoreCorrectionNextLayer
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedCrossGain
import Mathlib.Tactic

/-!
# Sharp quadratic remainder of ONE original global physical Hartree PDE correction

The preceding general physical one-step theorem deliberately downgraded the
true quadratic remainder s^(-2*rho) to s^(-(rho+kappa_phys)) to fit the
arbitrary-layer ledger. The locked single-orbit proof requires only rho=9/8:
then the true quadratic remainder has the target exponent 9/4 directly.

This theorem does NOT assume a higher-order residual. It derives that
exponent from the exact full nonlocal Hartree Taylor remainder and two
actual speed/correction cross terms after the principal linearized
*original PDE equation* is solved. The exact principal equation remains
a visible physical four-zone matching obligation; global weighted norms
and threshold-coordinate Lipschitz bounds remain separate obligations.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Sharp s^(-2*rho) instead of downgrading to s^(-(rho+kappa_phys)).
Every term is from the same original nonlocal radial Hartree PDE. -/
theorem actual_Hartree_one_global_PDE_quadratic_remainder_sharp
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega s r rho Cspeed CHd CH M : ℝ)
    (hs : 1 ≤ s) (hrho : 0 ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hM : 0 ≤ M) (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x)
    (hPrincipal :
      actualHartreeOneGlobalCoreCorrectionPrincipal
        U H b omega db domega s r =
        -complexRadialRenormalizedResidual U b omega s r) :
    ‖complexRadialRenormalizedResidual
        (fun t x => U t x + H t x)
        (b + db) (omega + domega) s r‖ ≤
      (Cspeed * (CHd + CH) +
        63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
        s ^ (-2 * rho) := by
  have hs0 : 0 ≤ s := by linarith
  have hsPow0 : 0 ≤ s ^ (-rho) := Real.rpow_nonneg hs0 _
  have hsPowOne : s ^ (-rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  let e : ℝ := CH * s ^ (-rho)
  have he : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg hCH hsPow0
  have heCH : e ≤ CH := by
    dsimp [e]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsPowOne hCH
  have hHBscaled : ∀ x : ℝ, 0 < x → ‖H s x‖ ≤ e * bubble x := by
    intro x hx
    simpa only [e, mul_assoc] using hHB x hx
  have hTaylorRaw :=
    actual_Hartree_complex_Taylor_bubble_bound
      (U s) (H s) hUmeas hHmeas M e hM he hUB hHBscaled r hr
  have hSum : M + e ≤ M + CH := by linarith only [heCH]
  have hSumPow : (M + e) ^ 5 ≤ (M + CH) ^ 5 :=
    pow_le_pow_left₀ (add_nonneg hM he) hSum 5
  have he2 : e ^ 2 = CH ^ 2 * s ^ (-2 * rho) := by
    dsimp [e]
    rw [mul_pow]
    have hp : (s ^ (-rho)) ^ 2 = s ^ (-2 * rho) := by
      rw [← Real.rpow_mul_natCast hs0 (-rho) 2]
      congr 1
      ring
    rw [hp]
  have hTaylor :
      ‖actualHartreeComplexTaylorRemainder (U s) (H s) r‖ ≤
        (63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-2 * rho) := by
    calc
      _ ≤ 63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 := hTaylorRaw
      _ ≤ 63 * (M + CH) ^ 5 * e ^ 2 * bubble r ^ 5 := by
        have hbubble : 0 ≤ bubble r := bubble_nonneg r
        have hfactor : 0 ≤ 63 * e ^ 2 * bubble r ^ 5 := by
          positivity
        calc
          63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 =
              (M + e) ^ 5 * (63 * e ^ 2 * bubble r ^ 5) := by ring
          _ ≤ (M + CH) ^ 5 * (63 * e ^ 2 * bubble r ^ 5) :=
            mul_le_mul_of_nonneg_right hSumPow hfactor
          _ = _ := by ring
      _ = (63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-2 * rho) := by
        rw [he2]
        ring
  have hHpoint : ‖H s r‖ ≤ CH * s ^ (-rho) := by
    calc
      ‖H s r‖ ≤ CH * s ^ (-rho) * bubble r := hHB r hr
      _ ≤ CH * s ^ (-rho) * 1 :=
        mul_le_mul_of_nonneg_left (bubble_le_one r)
          (mul_nonneg hCH hsPow0)
      _ = CH * s ^ (-rho) := by ring
  have hCross :=
    actual_Hartree_speed_cross_quadratic_time_order
      H db domega s r rho Cspeed CHd CH hs hrho
      hCs hCHd hCH hSpeed hDilation hHpoint
  have hExact :=
    actual_Hartree_one_global_core_correction_remainder_exact
      U H b omega db domega s r hr
      hUtime hHtime hUspace hHspace hUsecond hHsecond
  have hIdentity :
      actualHartreeOneGlobalCoreCorrectionRemainder
          U H b omega db domega s r =
        complexRadialRenormalizedResidual
          (fun t x => U t x + H t x)
          (b + db) (omega + domega) s r := by
    unfold actualHartreeOneGlobalCoreCorrectionRemainder
    rw [hPrincipal]
    ring
  rw [hIdentity] at hExact
  rw [hExact]
  calc
    _ ≤ ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
          (domega : ℂ) * H s r‖ +
        ‖actualHartreeComplexTaylorRemainder (U s) (H s) r‖ :=
      norm_add_le _ _
    _ ≤ (Cspeed * (CHd + CH)) * s ^ (-2 * rho) +
        (63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-2 * rho) :=
      add_le_add hCross hTaylor
    _ = (Cspeed * (CHd + CH) +
          63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
            s ^ (-2 * rho) := by ring

/-- Exact desired 9/4 order for the locked single-orbit exponent rho=9/8.
No positive next-residual order is supplied as a premise. -/
theorem actual_Hartree_one_global_PDE_locked_nine_fourths
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega s r Cspeed CHd CH M : ℝ)
    (hs : 1 ≤ s)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hM : 0 ≤ M) (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-(9 / 8 : ℝ)))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤
        CHd * s ^ (-(9 / 8 : ℝ)))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-(9 / 8 : ℝ)) * bubble x)
    (hPrincipal :
      actualHartreeOneGlobalCoreCorrectionPrincipal
        U H b omega db domega s r =
        -complexRadialRenormalizedResidual U b omega s r) :
    ‖complexRadialRenormalizedResidual
        (fun t x => U t x + H t x)
        (b + db) (omega + domega) s r‖ ≤
      (Cspeed * (CHd + CH) +
        63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
        s ^ (-(9 / 4 : ℝ)) := by
  have h := actual_Hartree_one_global_PDE_quadratic_remainder_sharp
    U H b omega db domega s r (9 / 8 : ℝ) Cspeed CHd CH M
    hs (by norm_num) hCs hCHd hCH hM hr
    hUtime hHtime hUspace hHspace hUsecond hHsecond
    hUmeas hHmeas hSpeed hDilation hUB hHB hPrincipal
  have hexp : (-2 * (9 / 8 : ℝ)) = -(9 / 4 : ℝ) := by norm_num
  simpa only [hexp] using h

end HBL.TypeIIDynamicSelection
