import HBL.TypeIIDynamicSelection.ActualOriginGreenMovingEndpointDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreen
import Mathlib.Tactic

/-!
# Moving origin-Green coefficient for an affine finite-profile source

Finite-profile source terms are repeatedly of the form
  F0(r) + alpha(s) G(r)
with fixed spatial shapes and differentiable scalar coefficients.
For this class the moving lower endpoint and the source-time variation can be
combined exactly by the already strict source linearity and endpoint FTC.

No general two-variable Leibniz theorem and no cross-error estimate are needed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_origin_Green_coeffB_moving_affine_source_hasDerivAt
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (hlohi : lo < hi)
    (F0 G : ℝ → ℂ) (hF0 : Continuous F0) (hG : Continuous G)
    (r0 alpha : ℝ → ℝ) (s r0dot alphadot : ℝ)
    (hr0 : r0 s ∈ Ioo lo hi)
    (hr0dot : HasDerivAt r0 r0dot s)
    (halpha : HasDerivAt alpha alphadot s) :
    HasDerivAt
      (fun t =>
        originGreenCoeffB K (r0 t)
          (fun r => F0 r + (alpha t : ℂ) * G r) hi)
      (r0dot • (-originGreenSourceB K F0 (r0 s)) +
        ((alphadot : ℂ) * originGreenCoeffB K (r0 s) G hi +
          (alpha s : ℂ) *
            (r0dot • (-originGreenSourceB K G (r0 s))))) s := by
  have hF0coeff :=
    actual_origin_Green_coeffB_moving_lower_hasDerivAt
      K hK hlohi F0 hF0 r0 s r0dot hr0 hr0dot
  have hGcoeff :=
    actual_origin_Green_coeffB_moving_lower_hasDerivAt
      K hK hlohi G hG r0 s r0dot hr0 hr0dot
  have halphaC :
      HasDerivAt (fun t => (alpha t : ℂ)) (alphadot : ℂ) s :=
    halpha.ofReal_comp
  have hprod :=
    halphaC.mul hGcoeff
  have hsum := hF0coeff.add hprod
  have hr0ev : ∀ᶠ t in 𝓝 s, r0 t ∈ Ioo lo hi :=
    hr0dot.continuousAt.eventually (Ioo_mem_nhds hr0.1 hr0.2)
  have heq : ∀ᶠ t in 𝓝 s,
      originGreenCoeffB K (r0 t)
          (fun r => F0 r + (alpha t : ℂ) * G r) hi =
        originGreenCoeffB K (r0 t) F0 hi +
          (alpha t : ℂ) * originGreenCoeffB K (r0 t) G hi := by
    filter_upwards [hr0ev] with t ht
    have hKt : OriginBasisOn K (r0 t) hi C := by
      intro r hr
      exact hK r ⟨(le_of_lt ht.1).trans hr.1, hr.2⟩
    have hF0I : IntervalIntegrable F0 volume (r0 t) hi :=
      Continuous.intervalIntegrable hF0 _ _
    have hGI : IntervalIntegrable G volume (r0 t) hi :=
      Continuous.intervalIntegrable hG _ _
    exact actual_moment_locked_regular_source_coefficient_add_mul_on
      K hKt ht.2.le F0 G hF0I hGI (alpha t : ℂ)
  exact hsum.congr_of_eventuallyEq heq

end HBL.TypeIIDynamicSelection
