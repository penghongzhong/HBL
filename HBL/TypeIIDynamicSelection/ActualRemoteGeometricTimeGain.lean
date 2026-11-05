import HBL.TypeIIDynamicSelection.PhysicalSourceMismatch
import HBL.TypeIIDynamicSelection.ExteriorQuadraticSlowGain
import HBL.KinematicTailEstimates
import Mathlib.Tactic

/-!
# Remote Hartree geometric error: strict positive time order

This is a thin consumer of the already proved physical remote-source
identity and the true quadratic monopole radius R_c=4/|c|.

The new content is only the time-power conversion
  |c(s)| <= C s^{-beta}, beta > 1/2
  => c(s)^2 <= C^2 s^{-1-(2 beta-1)}.

The physical scalar center mismatch |c-C_F| is NOT hidden or assumed
zero here.  The theorem isolates it as the only non-geometric remote
obstruction after the actual Hartree kernel estimate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualRemoteQuadraticTimeGain (beta : ℝ) : ℝ :=
  2 * beta - 1

theorem actual_remote_quadratic_time_gain_positive
    (beta : ℝ) (hbeta : 1 / 2 < beta) :
    0 < actualRemoteQuadraticTimeGain beta := by
  unfold actualRemoteQuadraticTimeGain
  linarith

theorem actual_remote_trapped_amplitude_squared_gain
    (s c C beta : ℝ) (hs : 1 ≤ s) (_hC : 0 ≤ C)
    (htrap : |c| ≤ C * s ^ (-beta)) :
    c ^ 2 ≤ C ^ 2 * s ^ (-1 - actualRemoteQuadraticTimeGain beta) := by
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hc2 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  have hpow : |c| ^ 2 ≤ (C * s ^ (-beta)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg c) htrap 2
  have hsPow :
      (s ^ (-beta)) ^ 2 =
        s ^ (-1 - actualRemoteQuadraticTimeGain beta) := by
    calc
      (s ^ (-beta)) ^ 2 =
          (s ^ (-beta)) ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ = s ^ ((-beta) * 2) :=
        (Real.rpow_mul hs0 (-beta) (2 : ℝ)).symm
      _ = s ^ (-1 - actualRemoteQuadraticTimeGain beta) := by
        congr 1
        unfold actualRemoteQuadraticTimeGain
        ring
  calc
    c ^ 2 = |c| ^ 2 := hc2
    _ ≤ (C * s ^ (-beta)) ^ 2 := hpow
    _ = C ^ 2 * (s ^ (-beta)) ^ 2 := by ring
    _ = _ := by rw [hsPow]

/-- The genuine remote Riesz potential-center gap has a strict integrable
time power on the fixed normalized core.  No mass matching is needed for
this geometric part. -/
theorem actual_exteriorHartree_gap_quadratic_time_gain
    (F : ℝ → ℝ) (hf : Measurable F)
    {c r s C beta : ℝ}
    (hF : IntegrableOn F (Ioi (monopoleQuadraticRadius c)))
    (hc : 0 < |c|) (hc1 : |c| ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 1 ≤ s) (hC : 0 ≤ C)
    (htrap : |c| ≤ C * s ^ (-beta)) :
    |radialHartreeExteriorPotential F (monopoleQuadraticRadius c) r -
       radialHartreeExteriorCenter F (monopoleQuadraticRadius c)| ≤
     (Real.pi * hartreeKappa / 4 * C ^ 2 *
        s ^ (-1 - actualRemoteQuadraticTimeGain beta) * r ^ 2) *
       ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| := by
  have hbase := actual_exteriorHartree_gap_quadratic_fixed_core
    F hf hF hc hc1 hr hr1
  have htime := actual_remote_trapped_amplitude_squared_gain
    s c C beta hs hC htrap
  have hk : 0 ≤ Real.pi * hartreeKappa / 4 := by
    unfold hartreeKappa
    positivity
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hmass : 0 ≤ ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| :=
    integral_nonneg (fun _ => abs_nonneg _)
  calc
    _ ≤ (Real.pi * hartreeKappa / 4 * c ^ 2 * r ^ 2) *
          ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| := hbase
    _ ≤ (Real.pi * hartreeKappa / 4 *
          (C ^ 2 * s ^ (-1 - actualRemoteQuadraticTimeGain beta)) * r ^ 2) *
          ∫ rho in Ioi (monopoleQuadraticRadius c), |F rho| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htime hk) hr2) hmass
    _ = _ := by ring

/-- The full genuine remote Hartree residual is reduced to the scalar center
mismatch plus a strictly positive-order geometric term. -/
theorem actual_fullHartree_effective_mismatch_time_split
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r C beta : ℝ}
    (hRpos : 0 < monopoleQuadraticRadius (c s))
    (hr : 0 < r) (_hr1 : r ≤ 1)
    (hsep : 2 * r ≤ monopoleQuadraticRadius (c s))
    (hZ : ∀ t rho, rho ≤ monopoleQuadraticRadius (c s) → Z t rho = 0)
    (hVmeas : Measurable (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s)))
    (hZmeas : Measurable (Z s))
    (hF : IntegrableOn (remoteComplexQuarticDifference
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s)) (Z s))
      (Ioi (monopoleQuadraticRadius (c s))))
    (hVrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c s)) (c s) rho : ℂ)‖ ^ 4)
      (Ioi (0 : ℝ)))
    (hc : 0 < |c s|) (hc1 : |c s| ≤ 1)
    (hs : 1 ≤ s) (hC : 0 ≤ C)
    (htrap : |c s| ≤ C * s ^ (-beta)) :
    let V := monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s)
    let F := remoteComplexQuarticDifference V (Z s)
    ‖monopoleComplexEffectiveIncrement c (b s) (omega s) s r -
      (complexRadialRenormalizedResidual
        (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
       complexRadialRenormalizedResidual
         (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r)‖ ≤
    (|c s - radialHartreeExteriorCenter F
        (monopoleQuadraticRadius (c s))| +
      (Real.pi * hartreeKappa / 4 * C ^ 2 *
        s ^ (-1 - actualRemoteQuadraticTimeGain beta) * r ^ 2) *
        ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho|) *
      (1 + monopoleRadialBoundConstant) ^ 3 := by
  dsimp only
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s)
  let F : ℝ → ℝ := remoteComplexQuarticDifference V (Z s)
  have hraw := actual_fullHartree_effective_mismatch_norm_le
    c b omega Z hRpos hr hsep hZ hVmeas hZmeas hF hVrow hc1
  have hFm : Measurable F :=
    remoteComplexQuarticDifference_measurable V (Z s) hVmeas hZmeas
  have hcenter :
      (4 * Real.pi * hartreeKappa * r ^ 2 *
        (1 / (monopoleQuadraticRadius (c s)) ^ 2)) *
        ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| ≤
      (Real.pi * hartreeKappa / 4 * C ^ 2 *
        s ^ (-1 - actualRemoteQuadraticTimeGain beta) * r ^ 2) *
        ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| := by
    have hRadius := actual_monopole_radius_inverse_square hc
    have htime := actual_remote_trapped_amplitude_squared_gain
      s (c s) C beta hs hC htrap
    have hcoef : 0 ≤ Real.pi * hartreeKappa / 4 := by
      unfold hartreeKappa
      positivity
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    have hmass : 0 ≤ ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| :=
      integral_nonneg (fun _ => abs_nonneg _)
    rw [hRadius]
    calc
      (4 * Real.pi * hartreeKappa * r ^ 2 * (c s ^ 2 / 16)) *
          ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| =
        (Real.pi * hartreeKappa / 4 * c s ^ 2 * r ^ 2) *
          ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| := by ring
      _ ≤ (Real.pi * hartreeKappa / 4 *
          (C ^ 2 * s ^ (-1 - actualRemoteQuadraticTimeGain beta)) * r ^ 2) *
          ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htime hcoef) hr2) hmass
      _ = _ := by ring
  have hsum :
      |c s - radialHartreeExteriorCenter F (monopoleQuadraticRadius (c s))| +
        (4 * Real.pi * hartreeKappa * r ^ 2 *
          (1 / (monopoleQuadraticRadius (c s)) ^ 2)) *
          ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| ≤
      |c s - radialHartreeExteriorCenter F (monopoleQuadraticRadius (c s))| +
        (Real.pi * hartreeKappa / 4 * C ^ 2 *
          s ^ (-1 - actualRemoteQuadraticTimeGain beta) * r ^ 2) *
          ∫ rho in Ioi (monopoleQuadraticRadius (c s)), |F rho| :=
    add_le_add le_rfl hcenter
  have hfactor : 0 ≤ (1 + monopoleRadialBoundConstant) ^ 3 := by
    have hmc := monopoleRadialBoundConstant_pos.le
    positivity
  exact hraw.trans (mul_le_mul_of_nonneg_right hsum hfactor)

end HBL.TypeIIDynamicSelection
