import HBL.TypeIIDynamicSelection.ActualHartreeRieszTimeUniformFromOriginalVelocity
import Mathlib.Tactic

/-!
# The true quartic Riesz time velocity from physical half-radial decay

The original three-dimensional radial Strauss decay |z(r)| and
|d_t z(r)| <= constant * sqrt(bubble(r)) yields a genuine
quartic density velocity dominated by bubble(r)^2.
Combining this direct polynomial inequality with the original
nonlocal Riesz row removes any independently assumed bound on
the TIME DERIVATIVE of the potential.

The half-radial decay and its time-velocity counterpart are still
physical-orbit inputs: for the full blowup construction they must be
produced from the true four-region PDE and differentiated profile.
No time-rate or modulation orbit is assumed here.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Explicit complex-coordinate quartic velocity bound, valid also at u=0. -/
theorem actual_Hartree_original_quartic_velocity_norm_bound
    (u du : ℂ) :
    |actualRadialQuarticMomentVelocity u du| ≤
      8 * ‖u‖ ^ 3 * ‖du‖ := by
  have hRe : |u.re * du.re| ≤ ‖u‖ * ‖du‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_re_le_norm u)
      (Complex.abs_re_le_norm du) (abs_nonneg _) (norm_nonneg _)
  have hIm : |u.im * du.im| ≤ ‖u‖ * ‖du‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_im_le_norm u)
      (Complex.abs_im_le_norm du) (abs_nonneg _) (norm_nonneg _)
  have hPolar :
      |u.re * du.re + u.im * du.im| ≤ 2 * ‖u‖ * ‖du‖ := by
    have hTriangle := abs_add_le (u.re * du.re) (u.im * du.im)
    linarith only [hTriangle, hRe, hIm]
  have hNonneg : 0 ≤ 4 * ‖u‖ ^ 2 := by positivity
  calc
    |actualRadialQuarticMomentVelocity u du| =
        (4 * ‖u‖ ^ 2) * |u.re * du.re + u.im * du.im| := by
          unfold actualRadialQuarticMomentVelocity
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
            abs_of_nonneg (sq_nonneg _)]
    _ ≤ (4 * ‖u‖ ^ 2) * (2 * ‖u‖ * ‖du‖) :=
      mul_le_mul_of_nonneg_left hPolar hNonneg
    _ = 8 * ‖u‖ ^ 3 * ‖du‖ := by ring

/-- A genuine physical quartic velocity, with both complex channels,
lies in the radial Riesz bubble-squared class under half-radial
bounds for the field AND its real temporal velocity. -/
theorem actual_Hartree_original_quartic_velocity_half_radial_to_bubble_sq
    (z dz : ℝ → ℂ) (M D : ℝ)
    (hM : 0 ≤ M) (_hD : 0 ≤ D)
    (hZ : ∀ r : ℝ, 0 < r →
      ‖z r‖ ≤ M * Real.sqrt (bubble r))
    (hDZ : ∀ r : ℝ, 0 < r →
      ‖dz r‖ ≤ D * Real.sqrt (bubble r)) :
    ∀ r : ℝ, 0 < r →
      |actualRadialQuarticMomentVelocity (z r) (dz r)| ≤
        (8 * M ^ 3 * D) * bubble r ^ 2 := by
  intro r hr
  have hW : 0 ≤ bubble r := bubble_nonneg r
  have hRoot : 0 ≤ Real.sqrt (bubble r) := Real.sqrt_nonneg _
  have hCubed :
      ‖z r‖ ^ 3 ≤ (M * Real.sqrt (bubble r)) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) (hZ r hr) 3
  have hProduct :
      ‖z r‖ ^ 3 * ‖dz r‖ ≤
        (M * Real.sqrt (bubble r)) ^ 3 *
          (D * Real.sqrt (bubble r)) :=
    mul_le_mul hCubed (hDZ r hr) (norm_nonneg _) (by positivity)
  have hRoot4 : (Real.sqrt (bubble r)) ^ 4 = bubble r ^ 2 := by
    calc
      (Real.sqrt (bubble r)) ^ 4 =
        ((Real.sqrt (bubble r)) ^ 2) ^ 2 := by ring
      _ = bubble r ^ 2 := by rw [Real.sq_sqrt hW]
  calc
    |actualRadialQuarticMomentVelocity (z r) (dz r)| ≤
        8 * ‖z r‖ ^ 3 * ‖dz r‖ :=
      actual_Hartree_original_quartic_velocity_norm_bound _ _
    _ ≤ 8 * ((M * Real.sqrt (bubble r)) ^ 3 *
          (D * Real.sqrt (bubble r))) := by
      calc
        8 * ‖z r‖ ^ 3 * ‖dz r‖ =
            8 * (‖z r‖ ^ 3 * ‖dz r‖) := by ring
        _ ≤ 8 * ((M * Real.sqrt (bubble r)) ^ 3 *
              (D * Real.sqrt (bubble r))) :=
          mul_le_mul_of_nonneg_left hProduct (by norm_num)
    _ = (8 * M ^ 3 * D) * (Real.sqrt (bubble r)) ^ 4 := by ring
    _ = (8 * M ^ 3 * D) * bubble r ^ 2 := by rw [hRoot4]

/-- Quantitative ORIGINAL inverse-square Riesz time differentiation
from the true field and velocity, with no assumed potential derivative
and no inverse-radius factor. -/
theorem actual_Hartree_radial_Riesz_time_uniform_from_half_radial_orbit
    (z dz : ℝ → ℝ → ℂ) (r s : ℝ) (hr : 0 < r)
    (I : Set ℝ) (hI : I ∈ 𝓝 s)
    (hZmeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (actualHartreeRieszQuarticTimeIntegrand z r t)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (actualHartreeRieszQuarticTimeIntegrand z r s) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (actualHartreeRieszQuarticTimeVelocity z dz r s)
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualHartreeRieszQuarticTimeVelocity z dz r t rho| ≤ B rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun t => (z t rho).re) (dz t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun t => (z t rho).im) (dz t rho).im t)
    (M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hVelOriginalMeas : Measurable
      (fun rho => actualRadialQuarticMomentVelocity (z s rho) (dz s rho)))
    (hZ : ∀ rho : ℝ, 0 < rho →
      ‖z s rho‖ ≤ M * Real.sqrt (bubble rho))
    (hDZ : ∀ rho : ℝ, 0 < rho →
      ‖dz s rho‖ ≤ D * Real.sqrt (bubble rho)) :
    HasDerivAt
      (fun t => radialHartreePotential (fun rho => ‖z t rho‖ ^ 4) r)
      (radialHartreePotential
        (fun rho => actualRadialQuarticMomentVelocity
          (z s rho) (dz s rho)) r) s ∧
    |radialHartreePotential
      (fun rho => actualRadialQuarticMomentVelocity
        (z s rho) (dz s rho)) r| ≤
          radialHartreeRowBoundConstant * (8 * M ^ 3 * D) := by
  have hQ := actual_Hartree_original_quartic_velocity_half_radial_to_bubble_sq
    (z s) (dz s) M D hM hD hZ hDZ
  exact actual_Hartree_radial_Riesz_time_derivative_uniform_from_quartic_velocity
    z dz r s hr I hI hZmeas hZint hVelMeas B hB hBound hRe hIm
    (8 * M ^ 3 * D) (by positivity) hVelOriginalMeas hQ

end HBL.TypeIIDynamicSelection
