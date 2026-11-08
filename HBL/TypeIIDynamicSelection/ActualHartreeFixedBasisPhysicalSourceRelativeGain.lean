import HBL.TypeIIDynamicSelection.ActualHartreeFixedKummerBasisMovingSpectrum
import HBL.KummerOriginGreen.UniformBound
import Mathlib.Tactic

/-!
# HBL §2.13: TRUE relative size of the fixed-basis spectral correction

The moving-spectral operator may be applied to the ORIGINAL
real-Cramer-selected Hartree quartic nonlocal Green field without
differentiating a moving Kummer fundamental pair. The exact defect is
  (b(mu(s),theta(s))-b(mu0,theta0)) * Green_K0[F_s].

Here the source selected field size is NOT an assumed independent
homogeneous amplitude: the ORIGINAL normalized Wronskian Green integral
bound produces it directly from a concrete bound M on the SAME
physical Hartree source on its ACTUAL moving annulus.

The resulting source-relative factor is exactly the physical
spectral parameter displacement, times the certified compact
fixed-basis constant and actual annulus length. This is a meaningful
spectral perturbation step in the original PDE without a prescribed
blowup rate, but the parameter displacement time decay and complete
three-region nonlinear residual are still separate analytic tasks.

No abstract GeneratedTerm.order field, new axiom, artificial
regional right inverse, or independent Green-field norm is used.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_fixed_basis_true_selected_spectral_relative_source_gain
    {mu0 theta0 scale : ℝ}
    (K : OriginKummerPair mu0 theta0 scale)
    (mu theta a ell c : ℝ → ℝ)
    (z : ℝ → ℝ → ℂ) (b w Z : ℝ → ℂ)
    (t B C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hBasis : OriginBasisOn K
      (actualHartreeSlowInnerRadius (ell t) / a t) B C)
    (hSource : ∀ r ∈ Icc
      (actualHartreeSlowInnerRadius (ell t) / a t) B,
      ‖actualHartreeTrueMovingAdjustedSource a ell c z b w Z t r‖ ≤ M) :
    ∀ r ∈ Icc
      (actualHartreeSlowInnerRadius (ell t) / a t) B,
      ‖actualHartreeFrozenBasisMovingSpectrumResidual K mu theta
        (fun u => actualHartreeSlowInnerRadius (ell u) / a u) B
        (fun u => actualHartreeTrueMovingAdjustedSource a ell c z b w Z u)
        t r -
        actualHartreeTrueMovingAdjustedSource a ell c z b w Z t r‖ ≤
      (|mu t - mu0| + |theta t - theta0|) *
        ((2 * C ^ 3 *
          (B - actualHartreeSlowInnerRadius (ell t) / a t)) * M) := by
  intro r hr
  let r0 : ℝ := actualHartreeSlowInnerRadius (ell t) / a t
  let F : ℝ → ℂ := actualHartreeTrueMovingAdjustedSource a ell c z b w Z t
  have hGreen :=
    originGreen_value_slope_norm_le K r0 B C M hC hM
      hBasis F hSource hr
  have hGreenValue :
      ‖originGreenValue K r0 B F r‖ ≤
        (2 * C ^ 3 * (B - r0)) * M := by
    have hn := norm_nonneg (originGreenSlope K r0 B F r)
    linarith only [hGreen, hn]
  have hOriginal :=
    actual_Hartree_fixed_basis_moving_spectrum_defect_bound
      K mu theta (fun u => actualHartreeSlowInnerRadius (ell u) / a u)
      B (fun u => actualHartreeTrueMovingAdjustedSource a ell c z b w Z u)
      t r
  have hMu : 0 ≤ |mu t - mu0| + |theta t - theta0| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hFinal := hOriginal.trans
    (mul_le_mul_of_nonneg_left hGreenValue hMu)
  simpa only [r0, F] using hFinal

end HBL.TypeIIDynamicSelection
