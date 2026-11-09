import HBL.TypeIIDynamicSelection.ActualHartreeOneGlobalCoreCorrectionNextLayer
import Mathlib.Tactic

/-!
# Original Hartree nonlinear correction: preserve the spatial speed terms

The accepted fixed-radius residual atom loses spatial decay when it replaces
the two modulation cross terms by constants. Here the SAME actual complex
background and correction remain in the original nonlocal quartic PDE, and
the exact speed terms retain their ACTUAL spatial profiles. In particular,
this lemma does not assume a new spatial envelope for radial dilation H,
does not assign a time gain to the weighted global norm, and does not claim
to construct the finite four-region physical correction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Spatially resolved genuine nonlocal Hartree remainder. The modulation
terms have the norms of the actual correction and its radial dilation,
rather than a non-integrable constant envelope. -/
theorem actual_Hartree_one_global_core_spatial_remainder_bound
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega s r M CH Cspeed rho : ℝ)
    (hs : 1 ≤ s) (hM : 0 ≤ M) (hCH : 0 ≤ CH) (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x) :
    ‖actualHartreeOneGlobalCoreCorrectionRemainder
        U H b omega db domega s r‖ ≤
      (Cspeed * s ^ (-rho)) *
        (‖complexRadialDilation (H s) r‖ + ‖H s r‖) +
      63 * (M + CH * s ^ (-rho)) ^ 5 *
        (CH * s ^ (-rho)) ^ 2 * bubble r ^ 5 := by
  have hs0 : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 1).trans hs
  have hspow : 0 ≤ s ^ (-rho) := Real.rpow_nonneg hs0 _
  let e : ℝ := CH * s ^ (-rho)
  have he : 0 ≤ e := mul_nonneg hCH hspow
  have hHscaled : ∀ x : ℝ, 0 < x → ‖H s x‖ ≤ e * bubble x := by
    intro x hx
    simpa only [e, mul_assoc] using hHB x hx
  have hTaylor :=
    actual_Hartree_complex_Taylor_bubble_bound
      (U s) (H s) hUmeas hHmeas M e hM he
      hUB hHscaled r hr
  have hExact :=
    actual_Hartree_one_global_core_correction_remainder_exact
      U H b omega db domega s r hr
      hUtime hHtime hUspace hHspace hUsecond hHsecond
  have hDb : |db| ≤ Cspeed * s ^ (-rho) := by
    calc
      |db| ≤ |db| + |domega| := le_add_of_nonneg_right (abs_nonneg domega)
      _ ≤ Cspeed * s ^ (-rho) := hSpeed
  have hDomega : |domega| ≤ Cspeed * s ^ (-rho) := by
    calc
      |domega| ≤ |db| + |domega| := le_add_of_nonneg_left (abs_nonneg db)
      _ ≤ Cspeed * s ^ (-rho) := hSpeed
  have hDNorm :
      ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r‖ =
        |db| * ‖complexRadialDilation (H s) r‖ := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul]
  have hHNorm :
      ‖(domega : ℂ) * H s r‖ = |domega| * ‖H s r‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hCross :
      ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
          (domega : ℂ) * H s r‖ ≤
        (Cspeed * s ^ (-rho)) *
          (‖complexRadialDilation (H s) r‖ + ‖H s r‖) := by
    calc
      _ ≤ ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r‖ +
           ‖(domega : ℂ) * H s r‖ := norm_add_le _ _
      _ = |db| * ‖complexRadialDilation (H s) r‖ +
          |domega| * ‖H s r‖ := by rw [hDNorm, hHNorm]
      _ ≤ (Cspeed * s ^ (-rho)) * ‖complexRadialDilation (H s) r‖ +
          (Cspeed * s ^ (-rho)) * ‖H s r‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hDomega (norm_nonneg _))
      _ = (Cspeed * s ^ (-rho)) *
          (‖complexRadialDilation (H s) r‖ + ‖H s r‖) := by ring
  rw [hExact]
  calc
    _ ≤
      ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
          (domega : ℂ) * H s r‖ +
        ‖actualHartreeComplexTaylorRemainder (U s) (H s) r‖ :=
      norm_add_le _ _
    _ ≤ (Cspeed * s ^ (-rho)) *
          (‖complexRadialDilation (H s) r‖ + ‖H s r‖) +
        63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 :=
      add_le_add hCross hTaylor
    _ = (Cspeed * s ^ (-rho)) *
          (‖complexRadialDilation (H s) r‖ + ‖H s r‖) +
        63 * (M + CH * s ^ (-rho)) ^ 5 *
          (CH * s ^ (-rho)) ^ 2 * bubble r ^ 5 := by
      dsimp [e]

end HBL.TypeIIDynamicSelection
