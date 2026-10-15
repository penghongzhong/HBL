import HBL.ScaleTestIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
Connection of the first modulation lemma's tested scale and phase derivatives
with the *actual* radial stationary bubble
W(r) = (1 + r^2)^(-1/2).

The paper's two resonant half-line functions are r ΛW and r W.  Their
normalizations yield the two diagonal -1 entries of the modulation
Jacobian.  This file uses the already verified parametric differentiation
under the compact testing integral; it does not assume the scale derivative.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace HBL.Modulation

/-- Smoothness required to apply the scalar radial testing theorem to the
explicit stationary bubble. -/
theorem bubble_contDiff : ContDiff ℝ 1 bubble := by
  have hA : ContDiff ℝ 1 (fun r : ℝ => 1 + r ^ 2) := by
    fun_prop
  have hPos (r : ℝ) : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hSqrt :
      ContDiff ℝ 1 (fun r : ℝ => Real.sqrt (1 + r ^ 2)) :=
    hA.sqrt (fun r => ne_of_gt (hPos r))
  have hSqrtNe (r : ℝ) : Real.sqrt (1 + r ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hPos r))
  change ContDiff ℝ 1 (fun r : ℝ => (Real.sqrt (1 + r ^ 2))⁻¹)
  exact hSqrt.inv hSqrtNe

/-- The half-line zero-energy phase resonance `r W(r)`. -/
def radialResonanceMinus (r : ℝ) : ℝ := r * bubble r

/-- The half-line zero-energy scale resonance `r ΛW(r)`. -/
def radialResonancePlus (r : ℝ) : ℝ :=
  r * dilationGenerator bubble r

/-- Compact-test normalization against the real scaling zero mode
gives the exact derivative -1 of the transported radial integral at W.
Unlike the earlier abstract implicit-function interface, this is a theorem
about the original explicit bubble and the manuscript's r ΛW test. -/
theorem bubble_normalized_scale_integral
    (R : ℝ) (hR : 0 ≤ R) (zeta : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta)
    (hzetaR : zeta R = 0)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonancePlus r) = 1) :
    HasDerivAt (transportedRadialTestIntegral R zeta bubble) (-1) 0 := by
  apply transportedRadialTestIntegral_scale_normalized
    R hR zeta bubble hzeta bubble_contDiff hzetaR
  simpa only [radialResonancePlus, dilationGenerator, mul_assoc] using hNorm

/-- At scale one the transported test of W is its ordinary phase-mode
pairing. -/
theorem bubble_phase_pairing_at_zero
    (R : ℝ) (zeta : ℝ → ℝ) :
    transportedRadialTestIntegral R zeta bubble 0 =
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonanceMinus r) := by
  change (∫ r in (0 : ℝ)..R,
      transportedRadialTest zeta 0 r * bubble r) =
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonanceMinus r)
  apply intervalIntegral.integral_congr
  intro r _
  simp [transportedRadialTest, radialResonanceMinus] <;> ring

/-- The imaginary-channel normalization against r W forces the exact
phase derivative -1 of the actual tested bubble. -/
theorem bubble_normalized_phase_derivative
    (R : ℝ) (zeta : ℝ → ℝ)
    (hNorm :
      (∫ r in (0 : ℝ)..R,
        zeta r * radialResonanceMinus r) = 1) :
    HasDerivAt
      (fun gamma : ℝ =>
        -(Real.sin gamma) * transportedRadialTestIntegral R zeta bubble 0)
      (-1) 0 := by
  have hVal : transportedRadialTestIntegral R zeta bubble 0 = 1 := by
    rw [bubble_phase_pairing_at_zero]
    exact hNorm
  have hDer :=
    ((Real.hasDerivAt_sin 0).neg).mul_const
      (transportedRadialTestIntegral R zeta bubble 0)
  simpa [hVal] using hDer

end HBL.Modulation
