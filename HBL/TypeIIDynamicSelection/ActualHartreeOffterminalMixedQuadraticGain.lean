import HBL.TypeIIDynamicSelection.ActualMixedQuarticGain
import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import Mathlib.Tactic

/-!
# Revised HBL 2.13: actual offterminal mixed Hartree quartic quadratic gain

The exact inverse-square Hartree density is
    |V(r)+Z_ell(r)|^4-|V(r)|^4-|Z_ell(r)|^4
with the TRUE 3D critical radiation
    Z_ell(r)=sqrt(ell)*z(t,ell*r).

The exact real-linear density 4V^3 Re Z_ell is separated in the original
Hartree polynomial identity, and the remaining quadratic/cubic density
has a genuine O(ell) gain from the physical scaling. In particular
this holds at ANY physical time t of one regular Hartree trajectory,
not merely for its explicitly chosen compact terminal datum.

The second theorem specializes V to the ACTUAL moment-generated
moving Hartree monopole profile, with the original cutoff and
physical inverse-square moment c=kappa_H*ell*m(t). It derives the
pointwise monopole bound from the already constructed radial profile.

Only the ordinary high-regularity physical sup bound B and smallness
of the actual monopole amplitude |c|<=1 are inputs. Both must be
produced along a regular physical Hartree orbit in the final
instantiation. No Type-II rate is assumed.

SCOPE: These are TRUE POINTWISE source estimates, NOT the full
weighted L2 offterminal mixed Riesz potential, C1 Kummer/outer
matching, or all positive generated-order estimates. Revised 2.13
is still OPEN after these new component proofs.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A physical offterminal radiation field supplies the second-order
Hartree quartic source O(ell), from the exact physical rescaling
and polynomial expansion; unlike an assumed s^-beta rate this is
valid for any ell in (0,1] and at every regular physical time t. -/
theorem actual_Hartree_offterminal_mixed_higher_from_physical_amplitude
    (t ell M B r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (V : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (hV : |V t r| ≤ M)
    (hz : ‖z t (ell * r)‖ ≤ B) :
    actualWholeRadiationMixedQuartic (V t)
        (rescalePhysicalRadiation ell (z t)) r =
      4 * V t r ^ 3 *
        (rescalePhysicalRadiation ell (z t) r).re +
      actualWholeRadiationMixedHigher (V t)
        (rescalePhysicalRadiation ell (z t)) r ∧
    |actualWholeRadiationMixedHigher (V t)
        (rescalePhysicalRadiation ell (z t)) r| ≤
      (6 * M ^ 2 * B ^ 2 + 4 * M * B ^ 3) * ell := by
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell (z t)
  have hSqrt : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg _
  have hSqrtOne : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hNorm :
      ‖Z r‖ = Real.sqrt ell * ‖z t (ell * r)‖ := by
    dsimp [Z, rescalePhysicalRadiation]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hSqrt]
  have hZsqrt : ‖Z r‖ ≤ Real.sqrt ell * B := by
    rw [hNorm]
    exact mul_le_mul_of_nonneg_left hz hSqrt
  have hZB : ‖Z r‖ ≤ B := by
    calc
      ‖Z r‖ ≤ Real.sqrt ell * B := hZsqrt
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hSqrtOne hB
      _ = B := by ring
  have hZ2 : ‖Z r‖ ^ 2 ≤ ell * B ^ 2 := by
    calc
      ‖Z r‖ ^ 2 ≤ (Real.sqrt ell * B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hZsqrt 2
      _ = ell * B ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hell.le]
  have hV2 : |V t r| ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hV 2
  have hVZ : |V t r| * ‖Z r‖ ≤ M * B :=
    mul_le_mul hV hZB (norm_nonneg _) hM
  have hCoeff :
      6 * |V t r| ^ 2 + 4 * |V t r| * ‖Z r‖ ≤
        6 * M ^ 2 + 4 * M * B := by
    nlinarith only [hV2, hVZ]
  have hSecond :
      |actualWholeRadiationMixedHigher (V t) Z r| ≤
        (6 * M ^ 2 * B ^ 2 + 4 * M * B ^ 3) * ell := by
    calc
      _ ≤ (6 * |V t r| ^ 2 + 4 * |V t r| * ‖Z r‖) *
            ‖Z r‖ ^ 2 :=
        actual_whole_radiation_mixed_higher_abs_le (V t) Z r
      _ ≤ (6 * M ^ 2 + 4 * M * B) * (ell * B ^ 2) :=
        mul_le_mul hCoeff hZ2 (sq_nonneg _) (by positivity)
      _ = (6 * M ^ 2 * B ^ 2 + 4 * M * B ^ 3) * ell := by ring
  exact ⟨actual_whole_radiation_mixed_linear_higher_exact (V t) Z r,
    hSecond⟩

/-- Specialization to the TRUE slow Hartree monopole V_c with
c=kappa_H*ell*m, instead of a freely prescribed bounded background.
The structural bound follows from the strict verified Fredholm
monopole profile, uniformly on the positive half-line. -/
theorem actual_Hartree_offterminal_moment_monopole_mixed_higher_length_gain
    (t ell m B r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) (hB : 0 ≤ B)
    (hc : |hartreeKappa * ell * m| ≤ 1)
    (z : ℝ → ℝ → ℂ)
    (hz : ‖z t (ell * r)‖ ≤ B) :
    |actualWholeRadiationMixedHigher
        (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (hartreeKappa * ell * m))
          (hartreeKappa * ell * m))
        (rescalePhysicalRadiation ell (z t)) r| ≤
      (6 * (1 + monopoleRadialBoundConstant) ^ 2 * B ^ 2 +
        4 * (1 + monopoleRadialBoundConstant) * B ^ 3) * ell := by
  let M : ℝ := 1 + monopoleRadialBoundConstant
  have hM : 0 ≤ M := by
    dsimp [M]
    have hMp := monopoleRadialBoundConstant_pos
    positivity
  let V : ℝ → ℝ → ℝ :=
    fun _ => monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (hartreeKappa * ell * m))
      (hartreeKappa * ell * m)
  have hV : |V t r| ≤ M := by
    exact monopolePerturbedRadialProfile_abs_le
      (R := monopoleQuadraticRadius (hartreeKappa * ell * m))
      hr hc
  have h := (actual_Hartree_offterminal_mixed_higher_from_physical_amplitude
    t ell M B r hell hellOne hM hB V z hV hz).2
  simpa only [V, M] using h

end HBL.TypeIIDynamicSelection
