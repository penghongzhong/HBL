import HBL.TypeIIDynamicSelection.ActualOneOrbitTerminalRadiation
import Mathlib.Tactic

/-!
# One-orbit Hartree cutoff with a fixed positive physical terminal moment

For the explicitly selected nonzero smooth annular radiation, the
previously proved physical-PDE terminal moment theorem yields a
neighborhood where the same radiation moment exceeds half of its
positive initial value. This result turns the actual moving-cutoff
transport estimate into an all-radii bound with a FIXED denominator
m0[g], rather than the unknown moment at each time.

The bound is conditional on genuine Hartree PDE regularity and on the
already proved positive-moment window. Neither the blowup rate nor a
complete 2.12 three-region source-cancellation theorem is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Genuine PDE cutoff transport, uniformly normalized by the concrete
nonzero terminal source g; the current-time moment lower bound is
exactly the one furnished by
`actual_one_orbit_Hartree_terminal_positive_moment_window`.
The physical flux is calculated from the original Hartree PDE rather
than supplied as a derivative of the scalar moment. -/
theorem actual_one_orbit_Hartree_PDE_cutoff_uniform_fixed_terminal_mass
    (ell b : ℝ → ℝ) (z zt : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s : ℝ}
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
    (hWindow :
      actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation / 2 <
        actualPhysicalInverseSquareMoment (z (time s))) :
    ∃ Cχ : ℝ, 0 < Cχ ∧ ∀ r : ℝ, 0 ≤ r →
      |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
        b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
        (4 * (ell s) ^ 2 *
          (|actualMomentLaplacianFlux (z (time s))| /
            actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation)) *
          Cχ := by
  have hGpos :
      0 < actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation :=
    actual_one_orbit_terminal_radiation_positive_moment
  have hMomentPos :
      0 < actualPhysicalInverseSquareMoment (z (time s)) := by
    linarith [hWindow, hGpos]
  obtain ⟨Cχ, hCχpos, hAll⟩ :=
    actual_Hartree_PDE_cutoff_uniform_all_r_length_gain
      ell b z zt time hEll hEllPos hTime I hI hZmeas hZint
      hVelMeas B hB hBound hRe hIm hPDE hMomentPos
  let f : ℝ := |actualMomentLaplacianFlux (z (time s))|
  let m : ℝ := actualPhysicalInverseSquareMoment (z (time s))
  let mG : ℝ := actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation
  have hm : 0 < m := hMomentPos
  have hmG : 0 < mG := hGpos
  have htwice : mG ≤ 2 * m := by
    dsimp [m, mG]
    linarith [hWindow]
  have hprod : f * mG ≤ f * (2 * m) :=
    mul_le_mul_of_nonneg_left htwice (abs_nonneg _)
  have hratio : f / m ≤ (2 * f) / mG := by
    apply (div_le_div_iff₀ hm hmG).2
    nlinarith [hprod]
  have hscale :
      2 * (ell s) ^ 2 * (f / m) ≤
        2 * (ell s) ^ 2 * ((2 * f) / mG) :=
    mul_le_mul_of_nonneg_left hratio (by positivity)
  refine ⟨Cχ, hCχpos, ?_⟩
  intro r hr
  have hPoint := hAll r hr
  rw [← actual_physical_inverse_square_radial_reduction (z (time s))] at hPoint
  change
    |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
      b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
      (2 * (ell s) ^ 2 * (f / m)) * Cχ at hPoint
  change
    |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
      b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
      (4 * (ell s) ^ 2 * (f / mG)) * Cχ
  calc
    _ ≤ (2 * (ell s) ^ 2 * (f / m)) * Cχ := hPoint
    _ ≤ (2 * (ell s) ^ 2 * ((2 * f) / mG)) * Cχ :=
      mul_le_mul_of_nonneg_right hscale hCχpos.le
    _ = (4 * (ell s) ^ 2 * (f / mG)) * Cχ := by ring

end HBL.TypeIIDynamicSelection
