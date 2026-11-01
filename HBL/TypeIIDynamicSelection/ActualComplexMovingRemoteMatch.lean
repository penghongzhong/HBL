import HBL.TypeIIDynamicSelection.ActualMovingRadiationPartition
import HBL.TypeIIDynamicSelection.RemoteComplexInteraction
import HBL.TypeIIDynamicSelection.ActualWholeRadiationSelfCubic
import Mathlib.Tactic

/-!
# Original 2.12: exact EXTERIOR Hartree source for a complex inner profile

The existing remote Hartree Riesz matching lemma assumed a real
background V. The genuine moving-cutoff regular-radiation profile has
a complex inner field U=V+Z_inner. Its exterior Q=Z-Z_inner still
vanishes below R(s), but U need not be real. This file proves the
real mathematical extension, keeping the original inverse-square
quartic potential and complex local cubic.

F(rho) = ||U(rho)+Q(rho)||^4-||U(rho)||^4.
On 2r <= R with Q=0 on (-infty,R],
  N(U+Q)(r)-N(U)(r)=P_ext[F](r) ||U(r)||^2 U(r).

The same theorem is then specialized to the actual nonterminal Hartree
radiation Z by a moving partition, with an explicit O(r^2) exterior
multipole error relative to its TRUE (not assumed matched) center.
The full residual difference is used, so the time/Laplacian/phase
terms cancel in the moving core.

No source weight gain, Kummer boundary matching, or Type II rate is
inserted as an axiom or asserted consequence.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Real quartic exterior density for an arbitrary complex inner Hartree
profile U and an arbitrary complex exterior perturbation Q. -/
def actualComplexRemoteDensity (U Q : ℝ → ℂ) (rho : ℝ) : ℝ :=
  ‖U rho + Q rho‖ ^ 4 - ‖U rho‖ ^ 4

theorem actualComplexRemoteDensity_measurable
    (U Q : ℝ → ℂ) (hU : Measurable U) (hQ : Measurable Q) :
    Measurable (actualComplexRemoteDensity U Q) := by
  unfold actualComplexRemoteDensity
  fun_prop

theorem actualComplexRemoteDensity_zero_in_core
    (U Q : ℝ → ℂ) {R : ℝ}
    (hQ : ∀ rho, rho ≤ R → Q rho = 0) :
    ∀ rho, rho ≤ R → actualComplexRemoteDensity U Q rho = 0 := by
  intro rho hrho
  simp [actualComplexRemoteDensity, hQ rho hrho]

/-- EXACT complex-background extension of the physical exterior
Hartree source identity, without replacing U by a real bubble. -/
theorem actual_complex_inner_remote_Hartree_source_exact
    (U Q : ℝ → ℂ) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hsep : 2 * r ≤ R)
    (hQ : ∀ rho, rho ≤ R → Q rho = 0)
    (hUmeas : Measurable U) (hQmeas : Measurable Q)
    (hF : IntegrableOn (actualComplexRemoteDensity U Q) (Ioi R))
    (hUrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * ‖U rho‖ ^ 4)
      (Ioi (0 : ℝ))) :
    complexRadialHartreeNonlinearity (fun rho => U rho + Q rho) r -
      complexRadialHartreeNonlinearity U r =
    (radialHartreeExteriorPotential
      (actualComplexRemoteDensity U Q) R r : ℂ) *
        actualWholeRadiationLocalCubic U r := by
  let F := actualComplexRemoteDensity U Q
  have hFm : Measurable F :=
    actualComplexRemoteDensity_measurable U Q hUmeas hQmeas
  have hFzero : ∀ rho, rho ≤ R → F rho = 0 :=
    actualComplexRemoteDensity_zero_in_core U Q hQ
  have hFindicator : (Ioi R).indicator F = F := by
    funext rho
    by_cases hh : rho ∈ Ioi R
    · simp [hh]
    · have hle : rho ≤ R := le_of_not_gt hh
      simp [hh, hFzero rho hle]
  have hPotF : radialHartreePotential F r =
      radialHartreeExteriorPotential F R r := by
    calc
      radialHartreePotential F r =
        radialHartreePotential ((Ioi R).indicator F) r := by rw [hFindicator]
      _ = _ := (radialHartreeExteriorPotential_eq_indicator F hR.le r).symm
  have hFrowOuter :=
    (radialHartreeExteriorPotential_quadratic_center
      F hFm hF hR hr hsep).2.1
  have hFrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * F rho)
      (Ioi (0 : ℝ)) := by
    have heq : (fun rho => rho * hartreeRadialLog r rho * F rho) =
        (Ioi R).indicator
          (fun rho => rho * hartreeRadialLog r rho * F rho) := by
      funext rho
      by_cases hh : rho ∈ Ioi R
      · simp [hh]
      · have hle : rho ≤ R := le_of_not_gt hh
        simp [hh, hFzero rho hle]
    rw [heq]
    exact (hFrowOuter.integrable_indicator measurableSet_Ioi).integrableOn
  have hDensity : (fun rho => ‖U rho + Q rho‖ ^ 4) =
      (fun rho => ‖U rho‖ ^ 4 + F rho) := by
    funext rho
    dsimp [F, actualComplexRemoteDensity]
    ring
  have hPotentialSum :
      radialHartreePotential (fun rho => ‖U rho + Q rho‖ ^ 4) r =
      radialHartreePotential (fun rho => ‖U rho‖ ^ 4) r +
        radialHartreeExteriorPotential F R r := by
    rw [hDensity]
    calc
      radialHartreePotential (fun rho => ‖U rho‖ ^ 4 + F rho) r =
          radialHartreePotential (fun rho => ‖U rho‖ ^ 4) r +
            radialHartreePotential F r := by
        unfold radialHartreePotential
        have heq : (fun rho => rho * hartreeRadialLog r rho *
            (‖U rho‖ ^ 4 + F rho)) =
          (fun rho => rho * hartreeRadialLog r rho * ‖U rho‖ ^ 4) +
            (fun rho => rho * hartreeRadialLog r rho * F rho) := by
          funext rho
          simp only [Pi.add_apply]
          ring
        rw [heq]
        change (2 * Real.pi * hartreeKappa / r) *
          (∫ rho in Ioi (0 : ℝ),
            rho * hartreeRadialLog r rho * ‖U rho‖ ^ 4 +
              rho * hartreeRadialLog r rho * F rho) = _
        rw [integral_add hUrow hFrow]
        ring
      _ = _ := by rw [hPotF]
  have hQr : Q r = 0 := hQ r (by linarith)
  unfold complexRadialHartreeNonlinearity actualWholeRadiationLocalCubic
  simp only [Pi.add_apply]
  rw [hQr, add_zero, hPotentialSum]
  push_cast
  ring

/-- The exact exterior quartic density obtained by removing the
moving remote part of ONE actual offterminal Hartree radiation field. -/
def actualMovingHartreeRemoteDensity
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (s rho : ℝ) : ℝ :=
  actualComplexRemoteDensity
    (actualOneLayerWithInnerRadiation V R Z s)
    (actualOneLayerRemoteRadiation R Z s) rho

/-- SAME actual physical Hartree residual: the moving complex inner
radiation leaves precisely its exterior Riesz source in the core. -/
theorem actual_moving_physical_complex_remote_Riesz_exact
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ)
    (hRc : ContinuousAt R s)
    (hR : ∀ t : ℝ, 0 < R t)
    (hr : 0 < r) (hsep : 2 * r ≤ R s)
    (hUmeas : Measurable (actualOneLayerWithInnerRadiation V R Z s))
    (hQmeas : Measurable (actualOneLayerRemoteRadiation R Z s))
    (hF : IntegrableOn (actualMovingHartreeRemoteDensity V R Z s) (Ioi (R s)))
    (hUrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖actualOneLayerWithInnerRadiation V R Z s rho‖ ^ 4)
      (Ioi (0 : ℝ))) :
    complexRadialRenormalizedResidual
        (actualOneLayerWithWholeRadiation V Z) b omega s r -
      complexRadialRenormalizedResidual
        (actualOneLayerWithInnerRadiation V R Z) b omega s r =
      (radialHartreeExteriorPotential
         (actualMovingHartreeRemoteDensity V R Z s) (R s) r : ℂ) *
        actualWholeRadiationLocalCubic
          (actualOneLayerWithInnerRadiation V R Z s) r := by
  let U := actualOneLayerWithInnerRadiation V R Z s
  let Q := actualOneLayerRemoteRadiation R Z s
  have hZero : ∀ rho, rho ≤ R s → Q rho = 0 :=
    actual_one_layer_true_remote_radiation_zero_on_moving_core R Z hR s
  have hWhole : (fun rho => U rho + Q rho) =
      actualOneLayerWithWholeRadiation V Z s := by
    funext rho
    exact (actual_one_layer_true_radiation_partition_exact V R Z s rho).symm
  have hNL := actual_complex_inner_remote_Hartree_source_exact
    U Q (hR s) hr hsep hZero hUmeas hQmeas hF hUrow
  rw [hWhole] at hNL
  have hRemote := actual_one_layer_true_moving_remote_residual_is_nonlinear
    V R Z b omega s r hRc hR hr hsep
  exact hRemote.trans hNL

/-- Physical exterior multipole mismatch: no false equality between
the dynamically selected slow coefficient and the external center
is assumed. The exact geometric remainder is quadratic in r. -/
theorem actual_moving_physical_complex_remote_center_error_le
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ)
    (hRc : ContinuousAt R s)
    (hR : ∀ t : ℝ, 0 < R t)
    (hr : 0 < r) (hsep : 2 * r ≤ R s)
    (hUmeas : Measurable (actualOneLayerWithInnerRadiation V R Z s))
    (hQmeas : Measurable (actualOneLayerRemoteRadiation R Z s))
    (hF : IntegrableOn (actualMovingHartreeRemoteDensity V R Z s) (Ioi (R s)))
    (hUrow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖actualOneLayerWithInnerRadiation V R Z s rho‖ ^ 4)
      (Ioi (0 : ℝ))) :
    ‖(complexRadialRenormalizedResidual
        (actualOneLayerWithWholeRadiation V Z) b omega s r -
      complexRadialRenormalizedResidual
        (actualOneLayerWithInnerRadiation V R Z) b omega s r) -
      (radialHartreeExteriorCenter
        (actualMovingHartreeRemoteDensity V R Z s) (R s) : ℂ) *
        actualWholeRadiationLocalCubic
          (actualOneLayerWithInnerRadiation V R Z s) r‖ ≤
    (4 * Real.pi * hartreeKappa * r ^ 2 *
      ∫ rho in Ioi (R s),
        |actualMovingHartreeRemoteDensity V R Z s rho| / rho ^ 2) *
      ‖actualWholeRadiationLocalCubic
          (actualOneLayerWithInnerRadiation V R Z s) r‖ := by
  let F : ℝ → ℝ := actualMovingHartreeRemoteDensity V R Z s
  let U : ℝ → ℂ := actualOneLayerWithInnerRadiation V R Z s
  have hSource := actual_moving_physical_complex_remote_Riesz_exact
    V R Z b omega s r hRc hR hr hsep hUmeas hQmeas hF hUrow
  have hFmeas : Measurable F :=
    actualComplexRemoteDensity_measurable U
      (actualOneLayerRemoteRadiation R Z s) hUmeas hQmeas
  have hpot :=
    (radialHartreeExteriorPotential_quadratic_center
      F hFmeas hF (hR s) hr hsep).2.2
  rw [hSource]
  have heq : (radialHartreeExteriorPotential F (R s) r : ℂ) *
      actualWholeRadiationLocalCubic U r -
      (radialHartreeExteriorCenter F (R s) : ℂ) *
        actualWholeRadiationLocalCubic U r =
      ((radialHartreeExteriorPotential F (R s) r -
        radialHartreeExteriorCenter F (R s) : ℝ) : ℂ) *
          actualWholeRadiationLocalCubic U r := by
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hpot (norm_nonneg _)

end HBL.TypeIIDynamicSelection
