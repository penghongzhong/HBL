import HBL.KummerOriginGreen.GreenBridge
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic

/-!
# Time derivative of the regular Green coefficient through source variation

For a fixed lower endpoint and fixed origin Kummer basis, the regular Green
coefficient is linear in the source.  Mathlib's dominated parametric interval
integral theorem therefore differentiates the coefficient directly from the
actual source curve.

This theorem does NOT assume that the Green coefficient is differentiable.
It assumes only:
* measurability/integrability of the actual Green integrand;
* a visible integrable majorant for its source derivative;
* pointwise differentiability of the source curve on one time neighborhood.

The moving-lower-endpoint contribution is handled independently by
ActualOriginGreenMovingEndpointDerivative.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology Interval

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_origin_Green_coeffB_fixed_lower_source_hasDerivAt
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 B s : ℝ)
    (F Fdot : ℝ → ℝ → ℂ)
    (S : Set ℝ) (bound : ℝ → ℝ)
    (hS : S ∈ 𝓝 s)
    (hMeas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable
        (originGreenSourceB K (F t)) (volume.restrict (Ι r0 B)))
    (hInt : IntervalIntegrable
      (originGreenSourceB K (F s)) volume r0 B)
    (hDotMeas : AEStronglyMeasurable
      (originGreenSourceB K (Fdot s)) (volume.restrict (Ι r0 B)))
    (hBound : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ S, ‖originGreenSourceB K (Fdot t) r‖ ≤ bound r)
    (hBoundInt : IntervalIntegrable bound volume r0 B)
    (hSourceDeriv : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ S, HasDerivAt (fun tau => F tau r) (Fdot t r) t) :
    HasDerivAt
      (fun t => originGreenCoeffB K r0 (F t) B)
      (originGreenCoeffB K r0 (Fdot s) B) s := by
  have hDiff : ∀ᵐ r ∂volume, r ∈ Ι r0 B →
      ∀ t ∈ S,
        HasDerivAt
          (fun tau => originGreenSourceB K (F tau) r)
          (originGreenSourceB K (Fdot t) r) t := by
    filter_upwards [hSourceDeriv] with r hr
    intro hrmem t ht
    have hd := hr hrmem t ht
    have hm :=
      hd.mul_const
        (originPhysicalValue K.y r / originGreenWronskian K r)
    simpa only [originGreenSourceB, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hm
  have hParam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) hS hMeas hInt hDotMeas hBound hBoundInt hDiff
  unfold originGreenCoeffB
  exact hParam.2

end HBL.TypeIIDynamicSelection
