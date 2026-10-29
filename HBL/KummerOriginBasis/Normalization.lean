import HBL.KummerOriginBasis.Wronskian
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace HBL.Profile.Kummer

/-- The reconstructed pair has the singular/regular normalization at zero,
including its weighted radial derivatives. -/
theorem origin_kummer_normalization {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (hR : 0 < R) :
    Tendsto (fun r : ℝ => originPhysicalValue K.y r - (r : ℂ)⁻¹) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (originPhysicalValue K.x) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * originPhysicalSlope K.y K.dy r)
      (𝓝[>] 0) (𝓝 (-1)) ∧
    Tendsto (fun r : ℝ => (r : ℂ) * originPhysicalSlope K.x K.dx r)
      (𝓝[>] 0) (𝓝 0) := by
  have hz : (0 : ℝ) ∈ Icc 0 R := ⟨le_rfl, hR.le⟩
  have slopeLimit (f : ℝ → ℂ) (v : ℂ)
      (hf : HasDerivWithinAt f v (Icc 0 R) 0) :
      Tendsto (fun r : ℝ => (f r - f 0) / (r : ℂ)) (𝓝[>] 0) (𝓝 v) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp
      ((hf.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hR)).mono Ioi_subset_Ici_self)
    change Tendsto (fun r : ℝ => (r - 0)⁻¹ • (f r - f 0)) _ _ at h
    simpa only [sub_zero, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using! h
  have hy := slopeLimit K.y (K.dy 0) (K.y_deriv 0 hz)
  have hx := slopeLimit K.x (K.dx 0) (K.x_deriv 0 hz)
  have hy0 : Tendsto K.y (𝓝[>] 0) (𝓝 1) := by
    simpa only [ContinuousWithinAt, K.y_zero] using
      ((K.y_deriv 0 hz).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hR)).continuousWithinAt.mono
        Ioi_subset_Ici_self
  have hdy0 : Tendsto K.dy (𝓝[>] 0) (𝓝 0) := by
    simpa only [ContinuousWithinAt, K.dy_zero] using
      ((K.dy_deriv 0 hz).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hR)).continuousWithinAt.mono
        Ioi_subset_Ici_self
  have hdx0 : Tendsto K.dx (𝓝[>] 0) (𝓝 1) := by
    simpa only [ContinuousWithinAt, K.dx_zero] using
      ((K.dx_deriv 0 hz).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hR)).continuousWithinAt.mono
        Ioi_subset_Ici_self
  have hc : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc0 : ContinuousAt (fun r : ℝ => (r : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
    simpa only [Complex.ofReal_zero] using! hc0.tendsto.mono_left nhdsWithin_le_nhds
  have hpsi : Tendsto (originPhysicalValue K.x) (𝓝[>] 0) (𝓝 1) := by
    simpa only [K.x_zero, K.dx_zero, sub_zero, originPhysicalValue] using! hx
  refine ⟨?_, hpsi, ?_, ?_⟩
  · simpa only [K.y_zero, K.dy_zero, sub_div, one_div, originPhysicalValue] using! hy
  · have h := (hc.mul hdy0).sub hy0
    simp only [zero_mul, zero_sub] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    dsimp [originPhysicalSlope]
    field_simp
  · have h := hdx0.sub hpsi
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    dsimp [originPhysicalSlope, originPhysicalValue]
    field_simp
end HBL.Profile.Kummer
