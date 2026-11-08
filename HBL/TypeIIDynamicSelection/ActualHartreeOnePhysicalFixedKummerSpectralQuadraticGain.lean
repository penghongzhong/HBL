import HBL.TypeIIDynamicSelection.ActualHartreeFixedKummerOneStepSpectralGain
import HBL.TypeIIDynamicSelection.ActualHartreeFixedBasisPhysicalSourceRelativeGain
import Mathlib.Tactic

/-!
# A real positive relative spectral gain for ONE physical Hartree source

This is NOT a formal packet with assigned order or an abstract arbitrary
forcing. Fix the actual normalized physical Kummer pair at mu0, theta0.
Take the genuine original 3D inverse-square quartic Hartree Riesz source
with its SAME uniquely Cramer-selected real scale and phase speeds,
and the actual slow inner interface ell(t)^(-1/16)/a(t).

The first real Kummer Green correction is
  u0(t) = G_K0[ F_true(t) ],
  u1(t) = G_K0[ (b(mu(t),theta(t))-b(mu0,theta0)) * u0(t) ].

The FULL perturbed frozen-radial Kummer equation for u0-u1 is
  L_mu(t),theta(t)[u0-u1] - F_true = -delta(t)*u1.

The RHS is proved quadratic in the actual physical real two-parameter
displacement, with its coefficient bounded by the same genuine
physical Hartree-source sup envelope M, the original Kummer norm C,
and the actual annulus length B-r0(t). No independent Green-field
norm or unknown chosen spectral error is inserted.

This is a quantified genuine relative gain for ONE local spectral
component only. The complete four-piece nonlocal Hartree residual,
its moving cutoff and time transport, remote interactions, direct
threshold Lipschitz and true Type-II rate remain unproved.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual SAME original quartic Hartree selected source and
matching geometry. The correction uses the actual original Green pair
and actual varying spectral coefficient, not a freely chosen packet. -/
def actualHartreeOnePhysicalSelectedFirstSpectralCorrectedField
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (B t r : ℝ) : ℂ :=
  actualHartreeOriginalSpectralFirstCorrectedField K
    (actualHartreeSlowInnerRadius (ell t) / a t) B
    (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t)
    (frozenZeroCoeff (mu t) (theta t)-frozenZeroCoeff mu0 theta0) r

/-- The actual physical PDE Kummer spectral residual of this first
corrected field; all original second-radial-jet terms are retained. -/
def actualHartreeOnePhysicalSelectedFirstSpectralResidual
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (B t r : ℝ) : ℂ :=
  actualHartreeOriginalSpectralCorrectedJetResidual K
    (actualHartreeSlowInnerRadius (ell t) / a t) B
    (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t)
    (frozenZeroCoeff (mu t) (theta t)-frozenZeroCoeff mu0 theta0) r

/-- The true first original Green correction eliminates the
LINEAR spectral PDE error, and its remaining PDE source is
QUADRATIC in the REAL spectral coordinates. -/
theorem actual_Hartree_one_physical_fixed_Kummer_spectral_quadratic_gain
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a ell c : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (b w Z : ℝ → ℂ)
    (t B C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hOrder : actualHartreeSlowInnerRadius (ell t) / a t ≤ B)
    (hBasis : OriginBasisOn K
      (actualHartreeSlowInnerRadius (ell t) / a t) B C)
    (hSource : ∀ r ∈ Icc
      (actualHartreeSlowInnerRadius (ell t) / a t) B,
      ‖actualHartreeTrueMovingAdjustedSource a ell c z b w Z t r‖ ≤ M) :
    ∀ r ∈ Icc
      (actualHartreeSlowInnerRadius (ell t) / a t) B,
      ‖actualHartreeOnePhysicalSelectedFirstSpectralResidual
          K mu theta a ell c z b w Z B t r -
          actualHartreeTrueMovingAdjustedSource a ell c z b w Z t r‖ ≤
        (|mu t - mu0| + |theta t - theta0|) ^ 2 *
          (2 * C ^ 3 *
            (B - actualHartreeSlowInnerRadius (ell t) / a t)) ^ 2 * M := by
  intro r hr
  let r0 : ℝ := actualHartreeSlowInnerRadius (ell t) / a t
  let F : ℝ → ℂ := actualHartreeTrueMovingAdjustedSource a ell c z b w Z t
  let d : ℂ := frozenZeroCoeff (mu t) (theta t) -
    frozenZeroCoeff mu0 theta0
  have hOriginal :=
    actual_Hartree_original_Kummer_first_spectral_correction_quadratic_bound
      K r0 B C M hC hM hOrder hBasis F hSource d r hr
  have hParam : ‖d‖ ≤ |mu t - mu0| + |theta t - theta0| := by
    dsimp [d]
    exact frozenZeroCoeff_difference_norm_le (mu t) (theta t) mu0 theta0
  have hSq : ‖d‖ ^ 2 ≤ (|mu t - mu0| + |theta t - theta0|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg d) hParam 2
  have hNum :
      ‖d‖ ^ 2 * (2 * C ^ 3 * (B - r0)) ^ 2 * M ≤
        (|mu t - mu0| + |theta t - theta0|) ^ 2 *
          (2 * C ^ 3 * (B - r0)) ^ 2 * M := by
    have h1 := mul_le_mul_of_nonneg_right hSq
      (sq_nonneg (2 * C ^ 3 * (B - r0)))
    exact mul_le_mul_of_nonneg_right h1 hM
  have hNorm :
      ‖actualHartreeOnePhysicalSelectedFirstSpectralResidual
          K mu theta a ell c z b w Z B t r -
          F r‖ ≤
        (|mu t - mu0| + |theta t - theta0|) ^ 2 *
          (2 * C ^ 3 * (B - r0)) ^ 2 * M := by
    exact hOriginal.trans hNum
  simpa only [actualHartreeOnePhysicalSelectedFirstSpectralResidual,
    r0, F, d] using hNorm

end HBL.TypeIIDynamicSelection
