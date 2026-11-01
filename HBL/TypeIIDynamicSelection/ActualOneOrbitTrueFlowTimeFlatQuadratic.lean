import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalPDEJets
import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Genuine Hartree flow: quantitative temporal flatness on the terminal core

The selected smooth, nonzero annular terminal datum has exact zero
radiation value and first physical-time derivative for 0<r<1/4,
as independently proved from the genuine radial Hartree PDE.

This file applies the native Mathlib Banach-valued mean value theorem
TWICE to the same physical trajectory; given a uniform bound on its
second time jet (a transparent strong regular-flow obligation), it
DERIVES a quadratic-in-(T-t) bound for the actual radiation on the
core, and transports that bound under the exact critical rescaling.

No prescribed Type II rate, artificial time-decay assumption, or
preservation of terminal compact support is used. The high-regularity
bound on the second time derivative is an explicit analytic interface
and must be instantiated from the genuine Hartree local theory.
This proves a meaningful component of manuscript 2.12, not its full
four-region source cancellation or its generated-term gains.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Two applications of the native normed-space mean value theorem
derive quadratic temporal gain from zero terminal value and velocity.
The second derivative is bounded but NOT required to vanish. -/
theorem physical_terminal_two_jet_quadratic_time_gain
    (f f₁ f₂ : ℝ → ℂ) (t T M : ℝ)
    (ht : t ≤ T) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc t T, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Icc t T, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Icc t T, ‖f₂ x‖ ≤ M)
    (hTerminal : f T = 0) (hTerminal₁ : f₁ T = 0) :
    ‖f t‖ ≤ M * (T - t) ^ 2 := by
  have hT : T ∈ Icc t T := ⟨ht, le_rfl⟩
  have ht' : t ∈ Icc t T := ⟨le_rfl, ht⟩
  have hfirst (x : ℝ) (hx : x ∈ Icc t T) :
      ‖f₁ x‖ ≤ M * (T - t) := by
    have hmean :=
      (convex_Icc t T).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := f₁) (f' := f₂)
        (fun y hy => (hf₁ y hy).hasDerivWithinAt) hf₂ hx hT
    have hTx : 0 ≤ T - x := sub_nonneg.mpr hx.2
    calc
      ‖f₁ x‖ = ‖f₁ T - f₁ x‖ := by simp [hTerminal₁]
      _ ≤ M * ‖T - x‖ := hmean
      _ = M * (T - x) := by rw [Real.norm_eq_abs, abs_of_nonneg hTx]
      _ ≤ M * (T - t) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hx.1 T) hM
  have hmain :=
    (convex_Icc t T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f₁) (C := M * (T - t))
      (fun y hy => (hf y hy).hasDerivWithinAt) hfirst ht' hT
  calc
    ‖f t‖ = ‖f T - f t‖ := by simp [hTerminal]
    _ ≤ (M * (T - t)) * ‖T - t‖ := hmain
    _ = M * (T - t) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht)]
      ring

/-- The actual selected Hartree terminal datum and its PDE-derived
first time jet vanish on the strict positive core, so a genuine
strong solution with a bounded second time jet has a derived
quadratic source gain. This statement never assumes that z(t)
remains compactly supported for t<T. -/
theorem actual_one_orbit_Hartree_core_quadratic_time_gain
    (z zt ztt : ℝ → ℝ → ℂ) (t T r M : ℝ)
    (ht : t ≤ T) (hM : 0 ≤ M)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho))
    (hr : 0 < r) (hcore : r < 1 / 4)
    (hFlow : ∀ x ∈ Icc t T,
      HasDerivAt (fun y => z y r) (zt x r) x)
    (hSecond : ∀ x ∈ Icc t T,
      HasDerivAt (fun y => zt y r) (ztt x r) x)
    (hBound : ∀ x ∈ Icc t T, ‖ztt x r‖ ≤ M) :
    ‖z t r‖ ≤ M * (T - t) ^ 2 := by
  have hZero : z T r = 0 := by
    rw [hTerminal]
    have hz := actual_one_orbit_terminal_bump_zero_core
      (r := r) hcore.le
    simp [actualOneOrbitTerminalRadiation, hz]
  have hVelocityZero : zt T r = 0 :=
    actual_one_orbit_terminal_Hartree_core_velocity_zero
      z zt T hTerminal hPDE hr hcore
  exact physical_terminal_two_jet_quadratic_time_gain
    (fun x => z x r) (fun x => zt x r) (fun x => ztt x r)
    t T M ht hM hFlow hSecond hBound hZero hVelocityZero

/-- The original energy-critical physical pullback, with exact
Z(s,r)=sqrt(ell) z(t,ell*r), inherits the temporal-flatness gain
where ell*r stays in the actual spatial core. No ell(s) decay or
modulation exponent is imposed. -/
theorem actual_one_orbit_Hartree_rescaled_core_quadratic_time_gain
    (z zt ztt : ℝ → ℝ → ℂ) (ell t T R M : ℝ)
    (_hell : 0 < ell) (ht : t ≤ T) (hM : 0 ≤ M)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho))
    (hcorepos : 0 < ell * R) (hcore : ell * R < 1 / 4)
    (hFlow : ∀ x ∈ Icc t T,
      HasDerivAt (fun y => z y (ell * R)) (zt x (ell * R)) x)
    (hSecond : ∀ x ∈ Icc t T,
      HasDerivAt (fun y => zt y (ell * R)) (ztt x (ell * R)) x)
    (hBound : ∀ x ∈ Icc t T, ‖ztt x (ell * R)‖ ≤ M) :
    ‖rescalePhysicalRadiation ell (z t) R‖ ≤
      (Real.sqrt ell * M) * (T - t) ^ 2 := by
  have hGain :=
    actual_one_orbit_Hartree_core_quadratic_time_gain
      z zt ztt t T (ell * R) M ht hM hTerminal
      hPDE hcorepos hcore hFlow hSecond hBound
  calc
    ‖rescalePhysicalRadiation ell (z t) R‖ =
        Real.sqrt ell * ‖z t (ell * R)‖ := by
      simp [rescalePhysicalRadiation, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ell)]
    _ ≤ Real.sqrt ell * (M * (T - t) ^ 2) :=
      mul_le_mul_of_nonneg_left hGain (Real.sqrt_nonneg ell)
    _ = (Real.sqrt ell * M) * (T - t) ^ 2 := by ring

end HBL.TypeIIDynamicSelection
