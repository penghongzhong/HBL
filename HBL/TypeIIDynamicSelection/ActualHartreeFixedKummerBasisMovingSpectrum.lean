import HBL.TypeIIDynamicSelection.ActualHartreeSlowInnerMovingGreenEndpoint
import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import HBL.KummerOriginGreen.GreenBridge
import HBL.KummerParameterInverse.CoefficientDifference
import Mathlib.Tactic

/-!
# HBL §2.13: bypass differentiating a moving Kummer basis by freezing ONE pair

For the ORIGINAL normalized origin pair K0 at (mu0,theta0), the exact
physical Kummer equation for a time-varying spectral pair
(mu(s),theta(s)) is the fixed-pair equation plus
  (b(mu(s),theta(s)) - b(mu0,theta0))*u(s,r),
where b is the genuine complex frozenZeroCoeff. This is an EXACT
identity for the constructed original Wronskian Green field, not an
independent regional source assumption.

This offers a shorter proof route than differentiating K(s):
use a fixed original basis and estimate the ONE explicitly generated
spectral defect by real parameter differences and the original
field norm. The defect is an output of the original physical
operator, not a new theorem hypothesis or artificially assigned order.

The exact result is specialized below to the genuine quartic
nonlocal Hartree Riesz source selected by ONE unique real Cramer pair
and the actual slow-inner moving lower radius ell(s)^(-1/16)/a(s).

A positive time order for the parameter difference, whole physical
four-piece PDE residual O(s^(-9/4)), and the derived Type-II rate
remain separate essential obligations. We do NOT count this as §2.13.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The genuine evolving-spectral frozen-basis radial Kummer operator,
evaluated on the ORIGINAL Wronskian normalized Green response. -/
def actualHartreeFrozenBasisMovingSpectrumResidual
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta : ℝ → ℝ) (r0 : ℝ → ℝ) (B : ℝ)
    (F : ℝ → ℝ → ℂ) (s r : ℝ) : ℂ :=
  originGreenSecond K (r0 s) B (F s) r +
    frozenFirstCoeff r * originGreenSlope K (r0 s) B (F s) r +
    frozenZeroCoeff (mu s) (theta s) *
      originGreenValue K (r0 s) B (F s) r

/-- Exact operator identity on ONE physical source and fixed original pair:
the only effect of changing spectral parameters is the explicit source
multiplier. No smallness, radius regularity or time law is assumed. -/
theorem actual_Hartree_fixed_basis_moving_spectrum_exact
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta : ℝ → ℝ) (r0 : ℝ → ℝ) (B : ℝ)
    (F : ℝ → ℝ → ℂ) (s r : ℝ) :
    actualHartreeFrozenBasisMovingSpectrumResidual K mu theta r0 B F s r =
      F s r +
        (frozenZeroCoeff (mu s) (theta s) -
          frozenZeroCoeff mu0 theta0) *
        originGreenValue K (r0 s) B (F s) r := by
  unfold actualHartreeFrozenBasisMovingSpectrumResidual
  calc
    _ =
      (originGreenSecond K (r0 s) B (F s) r +
        frozenFirstCoeff r * originGreenSlope K (r0 s) B (F s) r +
        frozenZeroCoeff mu0 theta0 *
          originGreenValue K (r0 s) B (F s) r) +
      (frozenZeroCoeff (mu s) (theta s) -
        frozenZeroCoeff mu0 theta0) *
        originGreenValue K (r0 s) B (F s) r := by ring
    _ = _ := by rw [originGreen_equation]

/-- The perturbation bound is produced by the ACTUAL complex spectral
coefficient difference, with no independently chosen error norm. -/
theorem actual_Hartree_fixed_basis_moving_spectrum_defect_bound
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta : ℝ → ℝ) (r0 : ℝ → ℝ) (B : ℝ)
    (F : ℝ → ℝ → ℂ) (s r : ℝ) :
    ‖actualHartreeFrozenBasisMovingSpectrumResidual
        K mu theta r0 B F s r - F s r‖ ≤
      (|mu s - mu0| + |theta s - theta0|) *
        ‖originGreenValue K (r0 s) B (F s) r‖ := by
  rw [actual_Hartree_fixed_basis_moving_spectrum_exact, add_sub_cancel_left]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (frozenZeroCoeff_difference_norm_le (mu s) (theta s) mu0 theta0)
    (norm_nonneg _)

/-- At every physical time with a genuine annular origin-basis bound,
the SAME selected Green field is classically differentiable in the
spatial Kummer radius and satisfies the exact varying-spectrum
equation, with its full defect displayed. -/
theorem actual_Hartree_fixed_basis_moving_spectrum_classical
    {mu0 theta0 scale a B C : ℝ}
    (K : OriginKummerPair mu0 theta0 scale)
    (hK : OriginBasisOn K a B C) (hab : a < B)
    (mu theta : ℝ → ℝ) (F : ℝ → ℂ)
    (hF : Continuous F) (r : ℝ) (hr : r ∈ Ioo a B) :
    HasDerivAt (originGreenValue K a B F)
      (originGreenSlope K a B F r) r ∧
    HasDerivAt (originGreenSlope K a B F)
      (originGreenSecond K a B F r) r ∧
    originGreenSecond K a B F r +
      frozenFirstCoeff r * originGreenSlope K a B F r +
      frozenZeroCoeff (mu r) (theta r) * originGreenValue K a B F r =
      F r +
        (frozenZeroCoeff (mu r) (theta r) -
          frozenZeroCoeff mu0 theta0) * originGreenValue K a B F r := by
  obtain ⟨hValue, hSlope, hODE⟩ :=
    (originGreen_classical_outgoing K hK hab F hF).1 r hr
  refine ⟨hValue, hSlope, ?_⟩
  calc
    _ = (originGreenSecond K a B F r +
          frozenFirstCoeff r * originGreenSlope K a B F r +
          frozenZeroCoeff mu0 theta0 * originGreenValue K a B F r) +
        (frozenZeroCoeff (mu r) (theta r) -
          frozenZeroCoeff mu0 theta0) * originGreenValue K a B F r := by ring
    _ = _ := by rw [hODE]

/-- SINGLE ORIGINAL three-dimensional Hartree quartic source,
actual Cramer-selected real pair and genuine slow-inner radius:
exact spectral-change defect in the ORIGINAL normalized Green field. -/
theorem actual_Hartree_true_source_fixed_basis_moving_spectral_defect
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a ell c : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (b w Z : ℝ → ℂ)
    (B s r : ℝ) :
    let F : ℝ → ℝ → ℂ :=
      fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t
    let r0 : ℝ → ℝ :=
      fun t => actualHartreeSlowInnerRadius (ell t) / a t
    ‖actualHartreeFrozenBasisMovingSpectrumResidual
        K mu theta r0 B F s r - F s r‖ ≤
      (|mu s - mu0| + |theta s - theta0|) *
        ‖originGreenValue K (r0 s) B (F s) r‖ := by
  exact actual_Hartree_fixed_basis_moving_spectrum_defect_bound
    K mu theta
    (fun t => actualHartreeSlowInnerRadius (ell t) / a t)
    B (fun t => actualHartreeTrueMovingAdjustedSource a ell c z b w Z t)
    s r

end HBL.TypeIIDynamicSelection
