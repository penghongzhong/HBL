import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Off-terminal radial Hartree radiation: spatial quadratic flatness

The relevant analytic fact for manuscript 2.12 is *spatial* Taylor
flatness of the genuine radial flow at each time, rather than persistence
of the annular terminal support or an imposed blowup exponent.

If f has zero derivative at the radial origin and uniformly bounded
second spatial derivative on [0,1], then the *derived* radial bounds are
  ||f(r)-f(0)|| <= M r²,   ||f'(r)|| <= M r,   ||f''(r)|| <= M.
The proof uses Mathlib's real-to-complex convex-set mean value theorem
TWICE, not an assumed quadratic estimate.

For the actual physical energy-critical rescaling,
 Z_ell(r)=sqrt(ell) z(t,ell*r),
the same estimates imply
 ||Z_ell(r)-sqrt(ell) z(t,0)|| <= M ell^(5/2) r²
for 0<=ell*r<=1. This is precisely the spatial order needed for the
flat source gain on a moving bubble core, subject only to the high
regularity/radial-origin premises shown explicitly in the theorem.

The regular Hartree local theory supplies a separate Sobolev-to-C²
realization and time-uniform bound obligation. These results are NOT
proofs of original 2.12 and do not assume the result of 2.12.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Real-interval mean-value theorem twice gives quadratic flatness
at a radial centre where the first spatial derivative is zero.
All derivative bounds are input from the *ordinary regularity* theory,
not from a fake source smallness or prescribed time exponent. -/
theorem actual_radial_C2_flatness_three_derivative_bounds
    (f : ℝ → ℂ) {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hFirst : deriv f 0 = 0)
    (hDiff : ∀ x ∈ Icc (0 : ℝ) R, DifferentiableAt ℝ f x)
    (hDiffSecond : ∀ x ∈ Icc (0 : ℝ) R,
      DifferentiableAt ℝ (deriv f) x)
    (hSecond : ∀ x ∈ Icc (0 : ℝ) R,
      ‖deriv (deriv f) x‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) :
    ‖f r - f 0‖ ≤ M * r ^ 2 ∧
      ‖deriv f r‖ ≤ M * r ∧
      ‖deriv (deriv f) r‖ ≤ M := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) R := ⟨le_rfl, hR⟩
  have hFirstPoint :
      ∀ x ∈ Icc (0 : ℝ) R, ‖deriv f x‖ ≤ M * x := by
    intro x hx
    have hMv :
        ‖deriv f x - deriv f 0‖ ≤ M * ‖x - 0‖ :=
      (convex_Icc (0 : ℝ) R).
        norm_image_sub_le_of_norm_deriv_le
        hDiffSecond hSecond h0 hx
    simpa only [hFirst, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg hx.1] using hMv
  have hLocalDiff :
      ∀ x ∈ Icc (0 : ℝ) r, DifferentiableAt ℝ f x := by
    intro x hx
    exact hDiff x ⟨hx.1, hx.2.trans hr.2⟩
  have hLocalFirst :
      ∀ x ∈ Icc (0 : ℝ) r, ‖deriv f x‖ ≤ M * r := by
    intro x hx
    have hbr : x ∈ Icc (0 : ℝ) R :=
      ⟨hx.1, hx.2.trans hr.2⟩
    exact (hFirstPoint x hbr).trans
      (mul_le_mul_of_nonneg_left hx.2 hM)
  have h0r : (0 : ℝ) ∈ Icc (0 : ℝ) r := ⟨le_rfl, hr.1⟩
  have hrr : r ∈ Icc (0 : ℝ) r := ⟨hr.1, le_rfl⟩
  have hMv :
      ‖f r - f 0‖ ≤ (M * r) * ‖r - 0‖ :=
    (convex_Icc (0 : ℝ) r).
      norm_image_sub_le_of_norm_deriv_le
      hLocalDiff hLocalFirst h0r hrr
  have hValue : ‖f r - f 0‖ ≤ M * r ^ 2 := by
    calc
      _ ≤ (M * r) * r := by
        simpa only [sub_zero, Real.norm_eq_abs,
          abs_of_nonneg hr.1] using hMv
      _ = M * r ^ 2 := by ring
  exact ⟨hValue, hFirstPoint r hr, hSecond r hr⟩

/-- For the genuine physical regular radiation at ANY admissible time,
the spatial flat part is quadratically small. The origin value is
allowed to be nonzero and is kept as a separate slow jet. -/
theorem actual_Hartree_offterminal_radial_flat_part
    (z : ℝ → ℝ → ℂ) (t M : ℝ) (hM : 0 ≤ M)
    (hFirst : deriv (z t) 0 = 0)
    (hDiff : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (z t) x)
    (hDiffSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (z t)) x)
    (hSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv (deriv (z t)) x‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖z t r - z t 0‖ ≤ M * r ^ 2 ∧
      ‖deriv (z t) r‖ ≤ M * r ∧
      ‖deriv (deriv (z t)) r‖ ≤ M := by
  exact actual_radial_C2_flatness_three_derivative_bounds
    (z t) (by norm_num : (0 : ℝ) ≤ 1) hM hFirst
    hDiff hDiffSecond hSecond hr

/-- Actual physical critical scaling gives precisely the ell^(5/2)
flat-gain coefficient, with NO terminal-support assumption:
  Z(s,r)=sqrt(ell)*z(t,ell*r).
The conclusion is valid at every regular physical time when ell*r
lies in the uniform radial C² domain. -/
theorem actual_Hartree_offterminal_rescaled_flat_part
    (z : ℝ → ℝ → ℂ) (t ell r M : ℝ)
    (hell : 0 < ell) (hM : 0 ≤ M)
    (hFirst : deriv (z t) 0 = 0)
    (hDiff : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (z t) x)
    (hDiffSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (z t)) x)
    (hSecond : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv (deriv (z t)) x‖ ≤ M)
    (hr : 0 ≤ r) (hcore : ell * r ≤ 1) :
    ‖rescalePhysicalRadiation ell (z t) r -
        (Real.sqrt ell : ℂ) * z t 0‖ ≤
      M * ell ^ 2 * Real.sqrt ell * r ^ 2 := by
  have hr0 : 0 ≤ ell * r := mul_nonneg hell.le hr
  have hflat := (actual_Hartree_offterminal_radial_flat_part
    z t M hM hFirst hDiff hDiffSecond hSecond
      ⟨hr0, hcore⟩).1
  calc
    ‖rescalePhysicalRadiation ell (z t) r -
        (Real.sqrt ell : ℂ) * z t 0‖ =
      Real.sqrt ell * ‖z t (ell * r) - z t 0‖ := by
        unfold rescalePhysicalRadiation
        rw [← mul_sub, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ell)]
    _ ≤ Real.sqrt ell * (M * (ell * r) ^ 2) :=
      mul_le_mul_of_nonneg_left hflat (Real.sqrt_nonneg ell)
    _ = M * ell ^ 2 * Real.sqrt ell * r ^ 2 := by ring

end HBL.TypeIIDynamicSelection
