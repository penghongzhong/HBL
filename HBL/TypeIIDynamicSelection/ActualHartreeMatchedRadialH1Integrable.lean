import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# True 3D radial Hdot1 density is INTEGRABLE for a compatible Kummer Green field

Unlike an inequality for a Lebesgue integral alone, this theorem proves
the actual weighted radial derivative-square is IntegrableOn on the
matching annulus. Therefore it excludes vacuous integration-by-zero
for non-integrable functions.

The native original matched Kummer certificate proves continuous
algebraic slope on the compact annulus and identifies it with
the actual derivative almost everywhere. The square of the
radius-weighted slope is therefore continuous on the compact interval.
Convergence of its integral is inherited via almost-everywhere
equality in the ORIGINAL Lebesgue measure restricted to the annulus.

No continuity of the original quartic Hartree forcing is assumed:
IntervalIntegrable forcing plus actual compatibility suffice.
No source-derived norm, time exponent, Type-II rate or unproved axiom
is added. The source-specific original Hartree theorem must still
instantiate the exact same F and Fredholm left jet.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Real (non-vacuous) weighted 3D radial gradient integrability from
the exact compatible source and almost-everywhere Green derivative. -/
theorem actual_Hartree_matched_radial_H1_density_integrable
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C : ℝ) (hab : a ≤ b)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) (hFI : IntervalIntegrable F volume a b)
    (U DU : ℂ)
    (hCompat : actualMomentLockedIntervalObstruction K a b F U DU = 0) :
    IntegrableOn
      (fun r : ℝ => r ^ 2 *
        ‖deriv (actualOriginMatchedKummerValue K a b F U DU) r‖ ^ 2)
      (Icc a b) volume := by
  let W : ℝ → ℂ := actualOriginMatchedKummerValue K a b F U DU
  let S : ℝ → ℂ := actualOriginMatchedKummerSlope K a b F U DU
  let g : ℝ → ℝ := fun r => r ^ 2 * ‖deriv W r‖ ^ 2
  let g0 : ℝ → ℝ := fun r => r ^ 2 * ‖S r‖ ^ 2
  have hCertificate :
      ActualOriginMatchedKummerCertificate K a b F U DU :=
    (actual_origin_matched_Kummer_certificate_iff
      K hK hab F hFI U DU).2 hCompat
  have hSlopeContinuous : ContinuousOn S (Icc a b) := by
    simpa only [S] using hCertificate.2.2.2.2.1
  have hG0Continuous : ContinuousOn g0 (Icc a b) := by
    dsimp [g0]
    exact ((continuous_id.pow 2).continuousOn).mul
      ((hSlopeContinuous.norm).pow 2)
  have hG0Integrable : IntegrableOn g0 (Icc a b) volume :=
    hG0Continuous.integrableOn_Icc
  have hDerivativeAE :
      ∀ᵐ r : ℝ ∂volume, r ∈ Icc a b →
        HasDerivAt W (S r) r := by
    filter_upwards [hCertificate.2.2.2.2.2] with r hr hrmem
    simpa only [W, S] using (hr hrmem).1
  have hGEqual : g =ᵐ[volume.restrict (Icc a b)] g0 := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hDerivativeAE] with r hr hrmem
    dsimp [g, g0]
    rw [(hr hrmem).deriv]
  have hGIntegrable : IntegrableOn g (Icc a b) volume :=
    hG0Integrable.congr hGEqual.symm
  simpa only [g, W] using hGIntegrable

end HBL.TypeIIDynamicSelection
