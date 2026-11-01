import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# True spatial flat radiation from the radial Hartree flow

The original 2.12 requires the spatial quadratic residual
  z^flat(t,r) = z(t,r) - z(t,0) χ(r) = O(r²)
on a physical core, also for the actual time jets. The solution need
NOT vanish away from its terminal time and no persistence of compact
support is asserted.

The native Banach mean value theorem twice yields, on the physical
core 0<=r<=1,
  |z(t,r)-z(t,0)| <= M r², |d_r z(t,r)| <= M r,
provided that the true radial flow is C² in r with its second radial
derivative bounded by M and the origin first radial derivative zero.
The origin condition follows from regular 3D radial smoothness and is
an EXPLICIT strong-flow/3D radial lift interface here.

Under the *actual* energy-critical rescaling
  Z(s,R)=sqrt(ell(s)) z(t(s),ell(s)*R),
the uniform spatial bound gives
  |Z^flat(s,R)| <= M ell(s)^(5/2) R²
with no prescribed blowup exponent. It is exactly the
ell^(5/2) R² source power requested by the manuscript,
not an imposed asymptotic rate. To finish original 2.12 one must
instantiate the C² bounds uniformly from the regular Hartree flow,
the spatial derivative time-jet version and true H+/H- Kummer/remote
source matching.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Quadratic radial spatial-flatness bound, from two genuine
normed-space mean value inequalities and the regular origin slope.
The O(r²), O(r) conclusion is DERIVED, not a hypothesis. -/
theorem actual_radial_spatial_quadratic_flatness
    (f f₁ f₂ : ℝ → ℂ) (r M : ℝ)
    (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Icc (0 : ℝ) r, ‖f₂ x‖ ≤ M)
    (hOrigin : f₁ 0 = 0) :
    ‖f r - f 0‖ ≤ M * r ^ 2 ∧
      ‖f₁ r‖ ≤ M * r := by
  have hZero : (0 : ℝ) ∈ Icc (0 : ℝ) r :=
    ⟨le_rfl, hr⟩
  have hR : r ∈ Icc (0 : ℝ) r := ⟨hr, le_rfl⟩
  have hfirst (x : ℝ) (hx : x ∈ Icc (0 : ℝ) r) :
      ‖f₁ x‖ ≤ M * r := by
    have hmean :=
      (convex_Icc : Convex ℝ (Icc (0 : ℝ) r)).
        norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := f₁) (f' := f₂)
        (fun y hy => (hf₁ y hy).hasDerivWithinAt)
        hf₂ hZero hx
    have hxpos : 0 ≤ x := hx.1
    calc
      ‖f₁ x‖ = ‖f₁ x - f₁ 0‖ := by simp [hOrigin]
      _ ≤ M * ‖x - 0‖ := hmean
      _ = M * x := by rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hxpos]
      _ ≤ M * r := mul_le_mul_of_nonneg_left hx.2 hM
  have hmean :=
    (convex_Icc : Convex ℝ (Icc (0 : ℝ) r)).
      norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f₁) (C := M * r)
      (fun x hx => (hf x hx).hasDerivWithinAt)
      hfirst hZero hR
  constructor
  · calc
      ‖f r - f 0‖ ≤ (M * r) * ‖r - 0‖ := hmean
      _ = M * r ^ 2 := by
        rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hr]
        ring
  · exact hfirst r hR

/-- The true Hartree regular radiation profile at an arbitrary
physical time admits the required spatial second-order flatness
whenever the cited high-regularity radial local flow supplies
its uniformly bounded second spatial derivative and regular origin
slope. No time-smallness is assumed. -/
theorem actual_Hartree_flow_spatial_quadratic_flatness
    (z zr zrr : ℝ → ℝ → ℂ) (time r M : ℝ)
    (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hFlow : ∀ x ∈ Icc (0 : ℝ) r,
      HasDerivAt (z time) (zr time x) x)
    (hFlowR : ∀ x ∈ Icc (0 : ℝ) r,
      HasDerivAt (zr time) (zrr time x) x)
    (hRegBound : ∀ x ∈ Icc (0 : ℝ) r,
      ‖zrr time x‖ ≤ M)
    (hRegularOrigin : zr time 0 = 0) :
    ‖z time r - z time 0‖ ≤ M * r ^ 2 ∧
      ‖zr time r‖ ≤ M * r := by
  exact actual_radial_spatial_quadratic_flatness
    (z time) (zr time) (zrr time) r M
    hr hM hFlow hFlowR hRegBound hRegularOrigin

/-- Exactly the source power of manuscript eq:flat-core-stage3,
at any time along the genuine regular radiation, on the actual
physical core ell*R<=1; no assumption of the form ell(s)~s^-beta
is made in the statement. -/
theorem actual_Hartree_rescaled_radial_spatial_flatness
    (z zr zrr : ℝ → ℝ → ℂ) (time ell R M : ℝ)
    (hell : 0 < ell) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hCore : ell * R ≤ 1)
    (hFlow : ∀ x ∈ Icc (0 : ℝ) (ell * R),
      HasDerivAt (z time) (zr time x) x)
    (hFlowR : ∀ x ∈ Icc (0 : ℝ) (ell * R),
      HasDerivAt (zr time) (zrr time x) x)
    (hRegBound : ∀ x ∈ Icc (0 : ℝ) (ell * R),
      ‖zrr time x‖ ≤ M)
    (hRegularOrigin : zr time 0 = 0) :
    ‖rescalePhysicalRadiation ell
      (fun r => z time r - z time 0) R‖ ≤
      (M * ell ^ 2 * Real.sqrt ell) * R ^ 2 := by
  have hEllR : 0 ≤ ell * R := mul_nonneg hell.le hR
  have hGain :=
    (actual_Hartree_flow_spatial_quadratic_flatness
      z zr zrr time (ell * R) M
      hEllR hM hFlow hFlowR hRegBound hRegularOrigin).1
  calc
    ‖rescalePhysicalRadiation ell
        (fun r => z time r - z time 0) R‖ =
      Real.sqrt ell * ‖z time (ell * R) - z time 0‖ := by
        simp [rescalePhysicalRadiation, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ell)]
    _ ≤ Real.sqrt ell * (M * (ell * R) ^ 2) :=
      mul_le_mul_of_nonneg_left hGain (Real.sqrt_nonneg ell)
    _ = (M * ell ^ 2 * Real.sqrt ell) * R ^ 2 := by ring

end HBL.TypeIIDynamicSelection
