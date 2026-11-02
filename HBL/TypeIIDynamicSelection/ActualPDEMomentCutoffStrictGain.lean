import HBL.TypeIIDynamicSelection.ActualCutoffUniformTransport
import HBL.TypeIIDynamicSelection.ActualOneLayerMovingParametrixTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# HBL original 2.12: actual Hartree PDE moving-cutoff positive time gain

The *original physical radiation quartic moment*, not an arbitrary
parameter c(s), fixes the moving cutoff chi_c(s,r).
The exact 3D radial Hartree PDE and valid dominated differentiation
force its MATERIAL (s,r) transport:
  |(partial_s+b*r*partial_r) chi_c|
  <= 2*C_chi*ell(s)^2*|m_0'(t(s))|/m_0(t(s)).

The same trapped physical length ell(s)<=C*s^(-beta) with beta>1/2,
combined with an actual finite relative moment-flux estimate
|m_0'|<=J*m_0, gives the STRICT POSITIVE full time gain
  |(partial_s+b*r*partial_r) chi_c|
  <= (2*C_chi*C^2*J) * s^(-1-(2*beta-1)).

The important exponent 2*beta-1>0 is derived, not put in an
abstract GeneratedTerm.order nor an imposed Type-II blowup speed.

The flux bound and trap window are visible ANALYTIC assumptions
from the selected physical Hartree orbit, not themselves proved
here. In particular no assertion of full original 2.12 closure
is made until ALL nonlocal/space/Frobenius/parameter-source atoms
have the same strictly positive gain.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The gain in the ORIGINAL Hartree moving cutoff material source.
It is positive precisely in the manuscript's beta>1/2 trap. -/
def actualPDEMomentCutoffGain (beta : ℝ) : ℝ := 2 * beta - 1

theorem actual_PDE_moment_cutoff_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    0 < actualPDEMomentCutoffGain beta := by
  unfold actualPDEMomentCutoffGain
  linarith

/-- Exact exponent comparison: trapped ell² has strictly more than
one power of renormalized time, without an assumed rate limit. -/
theorem actual_PDE_trapped_length_squared_positive_gain
    (s ell C beta : ℝ) (hs : 1 ≤ s) (hell : 0 ≤ ell)
    (hC : 0 ≤ C) (htrap : ell ≤ C * s ^ (-beta)) :
    ell ^ 2 ≤ C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta) := by
  have hpow : ell ^ 2 ≤ (C * s ^ (-beta)) ^ 2 :=
    pow_le_pow_left₀ hell htrap 2
  have hsp : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hsR :
      (s ^ (-beta)) ^ 2 =
        s ^ (-1 - actualPDEMomentCutoffGain beta) := by
    calc
      (s ^ (-beta)) ^ 2 =
          (s ^ (-beta)) ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ = s ^ ((-beta) * 2) :=
          (Real.rpow_mul hsp (-beta) (2 : ℝ)).symm
      _ = s ^ (-1 - actualPDEMomentCutoffGain beta) := by
          congr 1
          unfold actualPDEMomentCutoffGain
          ring
  calc
    ell ^ 2 ≤ (C * s ^ (-beta)) ^ 2 := hpow
    _ = C ^ 2 * (s ^ (-beta)) ^ 2 := by ring
    _ = C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta) := by rw [hsR]

/-- TRUE physical 3D inverse-square Hartree PDE yields the strict
positive material-cutoff gain after the actual source flux and
selected trapped scale are estimated. Everything on the LHS is the
real physical moment cutoff, not an invented regional error. -/
theorem actual_Hartree_PDE_moving_moment_cutoff_positive_order
    (ell b : ℝ → ℝ) (z zt : ℝ → ℝ → ℂ)
    (time : ℝ → ℝ) {s : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (I : Set ℝ)
    (hI : I ∈ 𝓝 (time s))
    (hZmeas : ∀ᶠ t in 𝓝 (time s),
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (fun rho => ‖z (time s) rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho =>
        actualRadialQuarticMomentVelocity (z (time s) rho) (zt (time s) rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt (time s) rho = Complex.I *
        (complexRadialLaplacian (z (time s)) rho +
          complexRadialHartreeNonlinearity (z (time s)) rho))
    (hmpos : 0 < actualPhysicalInverseSquareMoment (z (time s)))
    (C J beta : ℝ)
    (hTimeLarge : 1 ≤ s)
    (hC : 0 ≤ C)
    (hJ : 0 ≤ J)
    (hBeta : 1 / 2 < beta)
    (hTrap : ell s ≤ C * s ^ (-beta))
    (hTrueFlux :
      |actualMomentLaplacianFlux (z (time s))| ≤
        J * radialPhysicalQuarticMoment (z (time s))) :
    ∃ Cchi : ℝ, 0 < Cchi ∧
      0 < actualPDEMomentCutoffGain beta ∧
      ∀ r : ℝ, 0 ≤ r →
        |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
          b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
          (2 * Cchi * C ^ 2 * J) *
            s ^ (-1 - actualPDEMomentCutoffGain beta) := by
  obtain ⟨Cchi, hCchi, hCut⟩ :=
    actual_Hartree_PDE_cutoff_uniform_all_r_length_gain
      ell b z zt time hEll hEllPos hTime
      I hI hZmeas hZint hVelMeas B hB hBound hRe hIm
      hPDE hmpos
  have hm : 0 < radialPhysicalQuarticMoment (z (time s)) := by
    simpa only [actual_physical_inverse_square_radial_reduction] using hmpos
  have hRatio : |actualMomentLaplacianFlux (z (time s))| /
      radialPhysicalQuarticMoment (z (time s)) ≤ J :=
    (div_le_iff₀ hm).2 (by simpa only [mul_comm] using hTrueFlux)
  have hEll2 :
      (ell s) ^ 2 ≤ C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta) :=
    actual_PDE_trapped_length_squared_positive_gain
      s (ell s) C beta hTimeLarge hEllPos.le hC hTrap
  have hCoef : 0 ≤ 2 * J * Cchi := by positivity
  refine ⟨Cchi, hCchi,
    actual_PDE_moment_cutoff_gain_positive beta hBeta, ?_⟩
  intro r hr
  calc
    |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
      b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
      (2 * (ell s) ^ 2 *
        (|actualMomentLaplacianFlux (z (time s))| /
          radialPhysicalQuarticMoment (z (time s)))) * Cchi :=
        hCut r hr
    _ ≤ (2 * (ell s) ^ 2 * J) * Cchi := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRatio (by positivity)) hCchi.le
    _ = (ell s) ^ 2 * (2 * J * Cchi) := by ring
    _ ≤ (C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta)) *
        (2 * J * Cchi) :=
      mul_le_mul_of_nonneg_right hEll2 hCoef
    _ = (2 * Cchi * C ^ 2 * J) *
        s ^ (-1 - actualPDEMomentCutoffGain beta) := by ring

end HBL.TypeIIDynamicSelection
