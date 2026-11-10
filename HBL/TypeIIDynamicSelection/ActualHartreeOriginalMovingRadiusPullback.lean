import HBL.TypeIIDynamicSelection.ActualHartreeMovingRadiusNormalizedC2Stability
import Mathlib.Tactic

/-!
# Original physical moving-radius pullback, with exact source scaling

For E(x)=e(L*x), the ORIGINAL operator has effective scale a/L and
K_(a/L) E(x)=L^2 K_a e(L*x). Zero Cauchy data at the actual endpoint L
become zero data at 1. Only positive-radius differentiability is required.
This is the link from the physical matched field to the quantitative
source-supremum stability theorem; it is not a PDE time-decay assertion.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Profile.Kummer

private theorem actual_positive_radius_pullback_first
    (L x : ℝ) (hL : 0 < L) (hx : 0 < x) (e : ℝ → ℂ)
    (he : ∀ y ∈ Ioi (0 : ℝ), DifferentiableAt ℝ e y) :
    HasDerivAt (fun y => e (L * y))
      ((L : ℂ) * deriv e (L * x)) x := by
  exact (he (L * x) (mul_pos hL hx)).hasDerivAt.scomp x
    (hasDerivAt_const_mul L)

/-- Source-exact original Kummer scaling on a moving physical radius. -/
theorem actual_Hartree_original_moving_radius_operator_pullback
    (mu theta a L x : ℝ) (ha : 0 < a) (hL : 0 < L) (hx : 0 < x)
    (e : ℝ → ℂ)
    (he : ∀ y ∈ Ioi (0 : ℝ), DifferentiableAt ℝ e y)
    (he2 : DifferentiableAt ℝ (deriv e) (L * x)) :
    actualMatchedScaledKummerApply mu theta (a / L)
        (fun y => e (L * y)) x =
      (L ^ 2 : ℝ) • actualMatchedScaledKummerApply mu theta a e (L * x) := by
  let E : ℝ → ℂ := fun y => e (L * y)
  have hfirst (y : ℝ) (hy : 0 < y) :
      HasDerivAt E ((L : ℂ) * deriv e (L * y)) y :=
    actual_positive_radius_pullback_first L y hL hy e he
  have hnear : deriv E =ᶠ[𝓝 x]
      (fun y => (L : ℂ) * deriv e (L * y)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hfirst y hy).deriv
  have hInner : HasDerivAt (fun y => deriv e (L * y))
      ((L : ℂ) * deriv (deriv e) (L * x)) x :=
    he2.hasDerivAt.scomp x (hasDerivAt_const_mul L)
  have hsecond : HasDerivAt (deriv E)
      ((L : ℂ) * ((L : ℂ) * deriv (deriv e) (L * x))) x :=
    (hInner.const_mul (L : ℂ)).congr_of_eventuallyEq hnear
  change actualMatchedScaledKummerApply mu theta (a / L) E x = _
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecond.deriv, (hfirst x hx).deriv]
  have hValue : E x = e (L * x) := rfl
  rw [hValue]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_mul]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp [haC, hLC, hxC]

/-- The ORIGINAL moving endpoint's two zero jets become fixed endpoint
zero jets. No additional boundary datum or inverse is postulated. -/
theorem actual_Hartree_original_moving_radius_zero_jet_pullback
    (L : ℝ) (hL : 0 < L) (e : ℝ → ℂ)
    (he : ∀ y ∈ Ioi (0 : ℝ), DifferentiableAt ℝ e y)
    (hzero : e L = 0) (hdzero : deriv e L = 0) :
    (fun y => e (L * y)) 1 = 0 ∧
      deriv (fun y => e (L * y)) 1 = 0 := by
  constructor
  · simpa only [mul_one] using hzero
  · have h := (actual_positive_radius_pullback_first L 1 hL
      (by norm_num) e he).deriv
    simpa only [mul_one, hdzero, mul_zero] using h

end HBL.TypeIIDynamicSelection
