import HBL.KinematicPhysicalRateAlgebra
import HBL.KinematicPhysicalTimeLimit

/-!
Direct conversion of the actual reconstructed path to its physical power law.
The identity q = tau * lambda^2 avoids integrating a second asymptotic series
or assuming an inverse physical clock. No blowup trajectory is assumed to have
been constructed by this kinematic statement.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace HBL.Kinematic

/-- The physical power law follows from the two actual normalized limits.
All analytic premises concern the input path, rather than assumed limits of
its reconstructed scale or clock. -/
theorem slice_inverse_scale_physical_power_tendsto_one
    {A s₀ κ δ H Λ : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hΛ : 0 < Λ) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    Tendsto (fun s : ℝ => (sliceLambda A s₀ κ Λ h s)⁻¹ /
      ((Λ ^ A * A ^ (-((A + 1) / 2))) *
        slicePhysicalTime A s₀ κ Λ h s ^ ((A + 1) / 2))) atTop (𝓝 1) := by
  have hq := sliceClock_div_affine_tendsto_one (κ := κ) h hA hs₀ hδ hδ1 hH hbound
  have hl := (slice_kinematics_of_path h hA hs₀ hδ hδ1 hH hΛ hh hbound hsmall hκ).2.2
  have hqpow := hq.rpow_const (p := -((A + 1) / 2))
    (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hlpow := hl.rpow_const (p := A) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hprod := hqpow.mul hlpow
  simp only [Real.one_rpow, one_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop s₀] with s hs
  have hspos : 0 < s := hs₀.trans_le hs
  have hqpos : 0 < sliceClock A s₀ κ h s :=
    (mul_pos (by positivity : 0 < A / 2) hspos).trans_le
      (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs).1
  have hlpos := sliceLambda_pos hA hspos hΛ hqpos
  exact (inverseScale_div_physicalRate_eq hA hΛ hspos hlpos hqpos).symm

end HBL.Kinematic
