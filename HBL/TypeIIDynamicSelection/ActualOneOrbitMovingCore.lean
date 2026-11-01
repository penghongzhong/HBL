import HBL.TypeIIDynamicSelection.ActualOneOrbitLinearMixedCenter
import HBL.MonopoleMovingCutoffDerivative
import HBL.MonopoleRadialBound
import Mathlib.Tactic

/-!
# Actual nonzero-radiation moving Hartree monopole on its physical source

For the SAME explicitly constructed nonzero annular terminal radiation,
the original slow monopole coefficient is not assumed: it is precisely
c_ell = κ_H ∫ |Z_ell|^4 dr * (4π), obtained by critical scaling of the
full physical inverse-square Hartree moment.

The original moving-cutoff monopole profile
V_ell(r)=W(r)+c_ell (1-χ(|c_ell|r/4)) Ξ_mon(r)
is O(ell) throughout the actual support of Z_ell.

No fixed mu_infty, preset blowup speed, or artificially selected source
class is introduced. This lemma is a physical precursor to the genuine
full mixed-quartic Hartree source estimate, NOT complete manuscript 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual complete inverse-square radiation quartic charge of the
concentrated terminal field, with the original 3D normalization. -/
def actualOneOrbitTerminalSlowCharge (ell : ℝ) : ℝ :=
  actualRadiationCenter
    (rescalePhysicalRadiation ell actualOneOrbitTerminalRadiation)

/-- Exact original moving monopole profile, not a free V model. -/
def actualOneOrbitTerminalMovingProfile (ell r : ℝ) : ℝ :=
  monopolePerturbedRadialProfile
    (monopoleQuadraticRadius (actualOneOrbitTerminalSlowCharge ell))
    (actualOneOrbitTerminalSlowCharge ell) r

/-- The slow charge is a genuinely computed radiation moment. -/
theorem actual_one_orbit_terminal_slow_charge_eq
    (ell : ℝ) (hell : 0 < ell) :
    actualOneOrbitTerminalSlowCharge ell =
      hartreeKappa * ell *
        actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation := by
  unfold actualOneOrbitTerminalSlowCharge
  rw [actualRadiationCenter_equals_physical_slow_coefficient
    ell hell actualOneOrbitTerminalRadiation]
  rw [actual_physical_inverse_square_radial_reduction]

/-- The ACTUAL time-dependent cutoff of the original monopole profile
retains its full physical expression on the terminal radiation field. -/
theorem actual_one_orbit_terminal_moving_profile_identity
    (ell r : ℝ) :
    actualOneOrbitTerminalMovingProfile ell r =
      bubble r +
        actualOneOrbitTerminalSlowCharge ell *
          (1 - cutoff (|actualOneOrbitTerminalSlowCharge ell| * r / 4)) *
            monopoleRadialProfile r := by
  exact monopoleMovingCutoffProfile_eq
    (actualOneOrbitTerminalSlowCharge ell) r

/-- On the TRUE support of the rescaled annular radiation, even the
physical moving monopole V_c, not just the stationary bubble W, is O(ell).
The fixed coefficient is computed from the terminal m0[g]>0 and the
strictly verified global bound for the real monopole profile. -/
theorem actual_one_orbit_terminal_moving_profile_source_bound
    (ell r : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hOnSource : 1 / 4 < ell * r) :
    |actualOneOrbitTerminalMovingProfile ell r| ≤
      (4 + hartreeKappa *
        actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation *
          monopoleRadialBoundConstant) * ell := by
  let c := actualOneOrbitTerminalSlowCharge ell
  let m := actualPhysicalInverseSquareMoment actualOneOrbitTerminalRadiation
  let M := monopoleRadialBoundConstant
  have hc : c = hartreeKappa * ell * m := by
    dsimp [c, m]
    exact actual_one_orbit_terminal_slow_charge_eq ell hell
  have hcpos : 0 ≤ c := by
    dsimp [c, actualOneOrbitTerminalSlowCharge]
    exact actualRadiationCenter_nonneg _
  have hcabs : |c| = hartreeKappa * ell * m := by
    rw [abs_of_nonneg hcpos, hc]
  have hInv : 1 / r ≤ 4 * ell := by
    exact (div_le_iff₀ hr).2 (by nlinarith [hOnSource])
  have hW : |bubble r| ≤ 4 * ell := by
    rw [abs_of_nonneg (by unfold bubble; positivity)]
    exact (actual_one_orbit_bubble_le_inverse_radius r hr).trans hInv
  have hXi : |monopoleRadialProfile r| ≤ M :=
    monopoleRadialProfile_abs_le hr
  have hCut0 : 0 ≤ cutoff (|c| * r / 4) := by
    change 0 ≤ Real.smoothTransition (|c| * r / 4 - 1)
    exact Real.smoothTransition.nonneg _
  have hCut1 : cutoff (|c| * r / 4) ≤ 1 := by
    change Real.smoothTransition (|c| * r / 4 - 1) ≤ 1
    exact Real.smoothTransition.le_one _
  have hCut : |1 - cutoff (|c| * r / 4)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hCutXi :
      |1 - cutoff (|c| * r / 4)| * |monopoleRadialProfile r| ≤ M := by
    calc
      _ ≤ 1 * |monopoleRadialProfile r| :=
        mul_le_mul_of_nonneg_right hCut (abs_nonneg _)
      _ ≤ 1 * M :=
        mul_le_mul_of_nonneg_left hXi (by norm_num)
      _ = M := by ring
  change
    |monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r| ≤
      (4 + hartreeKappa * m * M) * ell
  rw [monopoleMovingCutoffProfile_eq]
  calc
    |bubble r + c * (1 - cutoff (|c| * r / 4)) * monopoleRadialProfile r| ≤
        |bubble r| +
          |c * (1 - cutoff (|c| * r / 4)) * monopoleRadialProfile r| :=
      abs_add_le _ _
    _ = |bubble r| + |c| * |1 - cutoff (|c| * r / 4)| *
      |monopoleRadialProfile r| := by
        rw [abs_mul, abs_mul]
    _ ≤ 4 * ell + (hartreeKappa * ell * m) * M := by
      apply add_le_add hW
      calc
        |c| * |1 - cutoff (|c| * r / 4)| *
            |monopoleRadialProfile r| =
          |c| * (|1 - cutoff (|c| * r / 4)| *
            |monopoleRadialProfile r|) := by ring
        _ ≤ |c| * M :=
          mul_le_mul_of_nonneg_left hCutXi (abs_nonneg c)
        _ = (hartreeKappa * ell * m) * M := by rw [hcabs]
    _ = (4 + hartreeKappa * m * M) * ell := by ring

end HBL.TypeIIDynamicSelection
