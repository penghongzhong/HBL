import HBL.TypeIIDynamicSelection.ActualHartreePureRadiationRieszLengthGain
import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszSpatialDecay
import Mathlib.Tactic

/-!
# HBL revised 2.13: full physical pure-radiation Hartree Riesz spatial decay

The actual energy-critical radial scaling is
  Z_ell(r) = sqrt(ell) z(ell*r),
  I[|Z_ell|^4](r) = ell * I[|z|^4](ell*r).

For any genuine radial Strauss/L-infinity regular field z, its complete
inverse-square quartic density is dominated by M*W^2. The original
positive radial Hartree kernel and the already certified W^2 potential
give, without replacing the convolution,
  |I[|Z_ell|^4](r)| <= M*C*ell/(1+ell*r).

This retains precisely the far-field decay lost by the earlier uniform
O(ell) bound; it neither prescribes a concentration law nor proves the
remaining regional matching or finite nonlinear profile.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The genuine pure-radiation quartic inverse-square potential has
both one length power and its correct rescaled global spatial tail. -/
theorem actual_Hartree_pure_radiation_Riesz_global_scaled_decay
    (ell r B A : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    |radialHartreePotential
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 4) r| ≤
      (2 * (B ^ 4 + A ^ 4) *
        actualHartreeBubbleSquaredRieszDecayConstant) * ell /
        (1 + ell * r) := by
  let M : ℝ := 2 * (B ^ 4 + A ^ 4)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hDensity (rho : ℝ) (hrho : 0 < rho) :
      |‖z rho‖ ^ 4| ≤ M * bubble rho ^ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ ‖z rho‖ ^ 4)]
    simpa only [M] using
      actual_Hartree_radial_quartic_envelope_from_Strauss
        z B A hB hA hSup hStrauss rho hrho
  have hRel :=
    actual_Hartree_Riesz_relative_bubble_sq_domination
      (fun rho : ℝ => ‖z rho‖ ^ 4)
      (hz.norm.pow_const 4) M hDensity (ell * r) (mul_pos hell hr)
  have hScalar :=
    actual_Hartree_bubble_squared_Riesz_spatial_decay
      (ell * r) (mul_pos hell hr)
  have hPot :
      |radialHartreePotential (fun rho => ‖z rho‖ ^ 4) (ell * r)| ≤
        (M * actualHartreeBubbleSquaredRieszDecayConstant) /
          (1 + ell * r) := by
    calc
      _ ≤ M * radialHartreePotential
          (fun rho => bubble rho ^ 2) (ell * r) := hRel
      _ ≤ M * (actualHartreeBubbleSquaredRieszDecayConstant /
          (1 + ell * r)) :=
        mul_le_mul_of_nonneg_left hScalar hM
      _ = (M * actualHartreeBubbleSquaredRieszDecayConstant) /
          (1 + ell * r) := by ring
  change |radialHartreePotential
      (fun rho => ‖rescalePhysicalRadiation ell z rho‖ ^ 4) r| ≤
      (M * actualHartreeBubbleSquaredRieszDecayConstant) * ell /
        (1 + ell * r)
  rw [actual_Hartree_critical_radiation_Riesz_scaling ell r hell z]
  rw [abs_mul, abs_of_pos hell]
  calc
    ell * |radialHartreePotential (fun rho => ‖z rho‖ ^ 4) (ell * r)| ≤
        ell * ((M * actualHartreeBubbleSquaredRieszDecayConstant) /
          (1 + ell * r)) := mul_le_mul_of_nonneg_left hPot hell.le
    _ = (M * actualHartreeBubbleSquaredRieszDecayConstant) * ell /
        (1 + ell * r) := by ring

end HBL.TypeIIDynamicSelection
