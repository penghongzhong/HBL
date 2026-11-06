import HBL.KummerOriginGreen.GreenBridge
import Mathlib.Tactic

/-!
# Moving lower-endpoint derivative of the origin-gauge Green coefficient

The complete obstruction and both compatibility columns use
  originGreenCoeffA K r1 F r0.
This file records the exact chain rule when the lower endpoint r0 moves.
The derivative is the genuine boundary Green density supplied by the already
verified interval FTC; no source truncation or asymptotic approximation enters.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_origin_Green_coeffA_moving_lower_hasDerivAt
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (hlohi : lo < hi)
    (F : ℝ → ℂ) (hF : Continuous F)
    (r0 : ℝ → ℝ) (s r0dot : ℝ)
    (hr0 : r0 s ∈ Ioo lo hi)
    (hr0dot : HasDerivAt r0 r0dot s) :
    HasDerivAt
      (fun t => originGreenCoeffA K hi F (r0 t))
      (r0dot • (-originGreenSourceA K F (r0 s))) s := by
  have hbase :=
    (originGreen_coefficients_hasDerivAt
      K hK hlohi F hF hr0).1
  exact hbase.scomp s hr0dot

theorem actual_origin_Green_coeffA_moving_lower_deriv_norm
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (hlohi : lo < hi)
    (F : ℝ → ℂ) (hF : Continuous F)
    (r0 : ℝ → ℝ) (s r0dot : ℝ)
    (hr0 : r0 s ∈ Ioo lo hi)
    (hr0dot : HasDerivAt r0 r0dot s) :
    ‖deriv (fun t => originGreenCoeffA K hi F (r0 t)) s‖ =
      |r0dot| * ‖originGreenSourceA K F (r0 s)‖ := by
  have h :=
    actual_origin_Green_coeffA_moving_lower_hasDerivAt
      K hK hlohi F hF r0 s r0dot hr0 hr0dot
  rw [h.deriv, norm_smul, Real.norm_eq_abs, norm_neg]


/-- The upper Green coefficient evaluated at a fixed upper point has the
same moving-lower-endpoint derivative, now through its LOWER integration
limit.  This is the coefficient that enters the selected Kummer upper jet. -/
theorem actual_origin_Green_coeffB_moving_lower_hasDerivAt
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (hlohi : lo < hi)
    (F : ℝ → ℂ) (hF : Continuous F)
    (r0 : ℝ → ℝ) (s r0dot : ℝ)
    (hr0 : r0 s ∈ Ioo lo hi)
    (hr0dot : HasDerivAt r0 r0dot s) :
    HasDerivAt
      (fun t => originGreenCoeffB K (r0 t) F hi)
      (r0dot • (-originGreenSourceB K F (r0 s))) s := by
  have hSources := originGreen_sources_continuous K hK F hF
  have hAt :
      ContinuousAt (originGreenSourceB K F) (r0 s) :=
    (hSources.1 (r0 s) ⟨hr0.1.le, hr0.2.le⟩).2
  have hCont :
      ContinuousOn (originGreenSourceB K F) (Icc (r0 s) hi) :=
    hSources.2.2.mono (Icc_subset_Icc hr0.1.le le_rfl)
  have hInt :
      IntervalIntegrable (originGreenSourceB K F) volume (r0 s) hi :=
    hCont.intervalIntegrable
  have hleft :=
    intervalIntegral.integral_hasDerivAt_left
      hInt hAt.stronglyMeasurableAtFilter hAt
  have hcomp := hleft.scomp s hr0dot
  change HasDerivAt
      (fun t => originGreenCoeffB K (r0 t) F hi)
      (r0dot • (-originGreenSourceB K F (r0 s))) s
  simpa only [originGreenCoeffB] using hcomp

theorem actual_origin_Green_coeffB_moving_lower_deriv_norm
    {mu theta scale lo hi C : ℝ}
    (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (hlohi : lo < hi)
    (F : ℝ → ℂ) (hF : Continuous F)
    (r0 : ℝ → ℝ) (s r0dot : ℝ)
    (hr0 : r0 s ∈ Ioo lo hi)
    (hr0dot : HasDerivAt r0 r0dot s) :
    ‖deriv (fun t => originGreenCoeffB K (r0 t) F hi) s‖ =
      |r0dot| * ‖originGreenSourceB K F (r0 s)‖ := by
  have h :=
    actual_origin_Green_coeffB_moving_lower_hasDerivAt
      K hK hlohi F hF r0 s r0dot hr0 hr0dot
  rw [h.deriv, norm_smul, Real.norm_eq_abs, norm_neg]

end HBL.TypeIIDynamicSelection
