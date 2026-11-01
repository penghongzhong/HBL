import HBL.TypeIIDynamicSelection.ActualComplexMovingRemoteMatch
import HBL.TypeIIDynamicSelection.ActualRadiationCenter
import Mathlib.Tactic

/-!
# Original HBL 2.12: actual whole-radiation monopole vs moving remote center

The original slow coefficient is NOT the exterior Hartree mass of a
new unrelated source; it is the physical total radiation moment:
  c_g(s)=4*pi*kappa_H * int_0^infinity |Z(s,rho)|^4 drho.

The actual moving exterior complex Hartree density is
  F_rem=|U+Q|^4-|U|^4,
  U=V+Z_inner, Q=Z-Z_inner, with Q=0 on rho<=R(s).

The difference c_g - center_ext(F_rem) therefore has the EXACT
physical error representation
  4*pi*kappa_H * int_0^infinity (|Z|^4-F_rem).

Its absolute value is bounded by the full integral of the
actual density mismatch, not set to zero or assumed small. This
identifies the remaining analytic source quantity required by the
monopole-Kummer-remote matching in original prop:one-layer-stage3.

All integrability inputs remain visible and refer to the SAME
off-terminal Hartree field. No imposed rate or support propagation.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The exact conversion from a total complex quartic radiation
moment to an exterior-supported Hartree monopole coefficient. -/
theorem actual_Hartree_full_minus_exterior_center_exact
    (Z : ℝ → ℂ) (F : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFzero : ∀ rho, rho ≤ R → F rho = 0)
    (hZint : IntegrableOn (fun rho => ‖Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hFint : IntegrableOn F (Ioi R)) :
    actualRadiationCenter Z - radialHartreeExteriorCenter F R =
      (4 * Real.pi * hartreeKappa) *
        ∫ rho in Ioi (0 : ℝ), (‖Z rho‖ ^ 4 - F rho) := by
  have hindicator : (Ioi R).indicator F = F := by
    funext rho
    by_cases h : rho ∈ Ioi R
    · simp [h]
    · simp [h, hFzero rho (le_of_not_gt h)]
  have hFint0 : IntegrableOn F (Ioi (0 : ℝ)) := by
    rw [← hindicator]
    exact (hFint.integrable_indicator measurableSet_Ioi).integrableOn
  have hwhole :
      (∫ rho in Ioi (0 : ℝ), F rho) =
        (∫ rho in Ioi R, F rho) := by
    calc
      _ = ∫ rho in Ioi (0 : ℝ), (Ioi R).indicator F rho := by
        rw [hindicator]
      _ = _ := by
        rw [setIntegral_indicator measurableSet_Ioi,
          inter_eq_right.mpr
            (show Ioi R ⊆ Ioi (0 : ℝ) from
              fun rho hrho => hR.trans_lt hrho)]
  unfold actualRadiationCenter radialHartreeCenter
    radialHartreeExteriorCenter
  rw [← hwhole, integral_sub hZint hFint0]
  ring

/-- The original actual monopole/exterior-center mismatch
is controlled by a SINGLE physical quartic density difference.
The estimate does not declare that mismatch small. -/
theorem actual_Hartree_full_minus_exterior_center_abs_le
    (Z : ℝ → ℂ) (F : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFzero : ∀ rho, rho ≤ R → F rho = 0)
    (hZint : IntegrableOn (fun rho => ‖Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hFint : IntegrableOn F (Ioi R)) :
    |actualRadiationCenter Z - radialHartreeExteriorCenter F R| ≤
      (4 * Real.pi * hartreeKappa) *
        ∫ rho in Ioi (0 : ℝ), |‖Z rho‖ ^ 4 - F rho| := by
  rw [actual_Hartree_full_minus_exterior_center_exact
    Z F R hR hFzero hZint hFint]
  have hc : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hc

/-- Apply the exact mismatch identity to the SAME real bubble core
and off-terminal complex Hartree radiation with the genuine moving
cutoff. Neither of the two center masses is replaced by a proxy. -/
theorem actual_one_layer_physical_monopole_remote_center_mismatch
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (s : ℝ)
    (hR : ∀ t, 0 < R t)
    (hZint : IntegrableOn (fun rho => ‖Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hFint : IntegrableOn
      (actualMovingHartreeRemoteDensity V R Z s) (Ioi (R s))) :
    actualRadiationCenter (Z s) -
      radialHartreeExteriorCenter
        (actualMovingHartreeRemoteDensity V R Z s) (R s) =
      (4 * Real.pi * hartreeKappa) *
        ∫ rho in Ioi (0 : ℝ),
          (‖Z s rho‖ ^ 4 -
            actualMovingHartreeRemoteDensity V R Z s rho) := by
  have hQ : ∀ rho, rho ≤ R s →
      actualOneLayerRemoteRadiation R Z s rho = 0 :=
    actual_one_layer_true_remote_radiation_zero_on_moving_core R Z hR s
  have hFzero : ∀ rho, rho ≤ R s →
      actualMovingHartreeRemoteDensity V R Z s rho = 0 :=
    actualComplexRemoteDensity_zero_in_core
      (actualOneLayerWithInnerRadiation V R Z s)
      (actualOneLayerRemoteRadiation R Z s) hQ
  exact actual_Hartree_full_minus_exterior_center_exact
    (Z s) (actualMovingHartreeRemoteDensity V R Z s)
    (R s) (hR s) hFzero hZint hFint

end HBL.TypeIIDynamicSelection
