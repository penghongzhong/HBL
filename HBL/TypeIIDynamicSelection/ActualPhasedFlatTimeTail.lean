import HBL.TypeIIDynamicSelection.ActualPhasedFlatTimeWeight
import HBL.KinematicTailEstimates
import Mathlib.Tactic

/-!
# Original 2.12: genuinely phased Hartree radiation has an integrable tail

Use the literal physical off-terminal radial Hartree flow, with the
actual time, scale, phase and moving core parameter functions. The
MVT-derived spatial flatness and the MODULATION trapping window imply
the strict power gain. Integrability and its full quantitative future
tail are DERIVED by the exact rpow integral, not inserted as assumptions.

The flow's C2 bound and continuity are visible standard high-regularity
local-theory inputs. This is not the weighted two-channel Kummer/remote
matching, nor an accepted complete original manuscript environment.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exactly the original regular-radiation phased-and-centre-cutoff
source along one physical modulation trajectory, with the real PDE
scale/time functions retained. -/
def actualHartreePhasedFlatTimeSource
    (z : ℝ → ℝ → ℂ) (time ell gamma R : ℝ → ℝ) (s : ℝ) : ℂ :=
  actualPhasedHartreeFlatRadiation
    (z (time s)) (ell s) (gamma s) (R s)

/-- The original actual physical radiation flat source, not a
model scalar power, is integrable on the renormalized future.
Its whole time integral enjoys the derived quantitative epsilon-flat
gain from the PDE trapping window. No blowup rate is fixed. -/
theorem actual_Hartree_phased_flat_physical_time_integrable
    (z zr zrr : ℝ → ℝ → ℂ)
    (time ell gamma R : ℝ → ℝ)
    (s0 M beta rho : ℝ)
    (hs0 : 1 ≤ s0) (hM : 0 ≤ M)
    (hbeta : 1 / 2 < beta) (hrho : 0 < rho)
    (hroom : rho < (5 * beta - 2) / 4)
    (hEll : ∀ s ∈ Ioi s0, 0 < ell s)
    (hScale : ∀ s ∈ Ioi s0, ell s ≤ s ^ (-beta))
    (hR : ∀ s ∈ Ioi s0, 0 ≤ R s)
    (hRWindow : ∀ s ∈ Ioi s0, R s ≤ s ^ rho)
    (hCore : ∀ s ∈ Ioi s0, ell s * R s ≤ 1)
    (hFlow : ∀ s ∈ Ioi s0, ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (z (time s)) (zr (time s) x) x)
    (hFlowR : ∀ s ∈ Ioi s0, ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (zr (time s)) (zrr (time s) x) x)
    (hRegBound : ∀ s ∈ Ioi s0, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖zrr (time s) x‖ ≤ M)
    (hRegularOrigin : ∀ s ∈ Ioi s0, zr (time s) 0 = 0)
    (hContinuous : ContinuousOn
      (fun s => ‖actualHartreePhasedFlatTimeSource
        z time ell gamma R s‖) (Ioi s0)) :
    IntegrableOn (fun s => ‖actualHartreePhasedFlatTimeSource
      z time ell gamma R s‖) (Ioi s0) ∧
    (∫ s in Ioi s0, ‖actualHartreePhasedFlatTimeSource
      z time ell gamma R s‖) ≤
      M * (s0 ^ (-(5 * beta / 2 - 2 * rho - 1)) /
        (5 * beta / 2 - 2 * rho - 1)) := by
  let ε : ℝ := 5 * beta / 2 - 2 * rho - 1
  have hε : 0 < ε :=
    actual_Hartree_flat_gain_pos_of_trap beta rho hbeta hrho hroom
  have hs0pos : 0 < s0 := lt_of_lt_of_le zero_lt_one hs0
  have hexp : -5 * beta / 2 + 2 * rho = -1 - ε := by
    dsimp [ε]
    ring
  have hBound : ∀ s ∈ Ioi s0,
      ‖actualHartreePhasedFlatTimeSource
        z time ell gamma R s‖ ≤ M * s ^ (-1 - ε) := by
    intro s hs
    have hsOne : 1 ≤ s := hs0.trans hs.le
    have h := actual_Hartree_phased_flat_source_time_gain
      z zr zrr (time s) s (ell s) (gamma s) (R s)
      M beta rho hsOne (hEll s hs) (hScale s hs)
      (hR s hs) (hRWindow s hs) (hCore s hs)
      hM (hFlow s hs) (hFlowR s hs)
      (hRegBound s hs) (hRegularOrigin s hs)
    change ‖actualHartreePhasedFlatTimeSource
      z time ell gamma R s‖ ≤ M * s ^ (-5 * beta / 2 + 2 * rho)
      at h
    rw [hexp] at h
    exact h
  have hPowerInt :
      IntegrableOn (fun s : ℝ => M * s ^ (-1 - ε)) (Ioi s0) :=
    ((integrableOn_Ioi_rpow_of_lt
      (show -1 - ε < -1 by linarith) hs0pos).const_mul M)
  have hInt :
      IntegrableOn (fun s => ‖actualHartreePhasedFlatTimeSource
        z time ell gamma R s‖) (Ioi s0) := by
    apply hPowerInt.mono'
      (hContinuous.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hBound s hs
  refine ⟨hInt, ?_⟩
  calc
    (∫ s in Ioi s0, ‖actualHartreePhasedFlatTimeSource
      z time ell gamma R s‖) ≤
      ∫ s in Ioi s0, M * s ^ (-1 - ε) := by
        apply integral_mono_ae hInt hPowerInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hBound s hs
    _ = M * (s0 ^ (-ε) / ε) := by
      rw [integral_const_mul,
        HBL.Kinematic.integral_Ioi_rpow_neg_one_sub hs0pos hε]
    _ = M * (s0 ^ (-(5 * beta / 2 - 2 * rho - 1)) /
        (5 * beta / 2 - 2 * rho - 1)) := rfl

end HBL.TypeIIDynamicSelection
