import HBL.KinematicSynchronizedSlice

/-!
Dependence of the actual synchronized parameter on the decaying path.
The tail difference is estimated from the difference of the two actual
integrated clocks, and then passed through the already proved inverse.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

theorem sliceIntegrand_path_abs_le
    {A s₀ κ s δ P c : ℝ} {h k : ℝ → ℝ}
    (hs : 0 < s) (hc : 0 < c)
    (hqh : c * s ≤ sliceClock A s₀ κ h s)
    (hqk : c * s ≤ sliceClock A s₀ κ k s)
    (hp : |clockPerturbation s₀ h s - clockPerturbation s₀ k s| ≤
      P * s ^ (1 - δ)) :
    |sliceIntegrand A s₀ κ h s - sliceIntegrand A s₀ κ k s| ≤
      (P * c⁻¹ ^ 2) * s ^ (-1 - δ) := by
  have hph := (mul_pos hc hs).trans_le hqh
  have hpk := (mul_pos hc hs).trans_le hqk
  have hid : sliceIntegrand A s₀ κ h s - sliceIntegrand A s₀ κ k s =
      -(clockPerturbation s₀ h s - clockPerturbation s₀ k s) *
        ((sliceClock A s₀ κ h s)⁻¹ * (sliceClock A s₀ κ k s)⁻¹) := by
    unfold sliceIntegrand
    field_simp [hph.ne', hpk.ne']
    simp only [sliceClock]
    ring
  have hi : (sliceClock A s₀ κ h s)⁻¹ * (sliceClock A s₀ κ k s)⁻¹ ≤
      (c * s)⁻¹ * (c * s)⁻¹ :=
    mul_le_mul (inv_anti₀ (mul_pos hc hs) hqh)
      (inv_anti₀ (mul_pos hc hs) hqk) (inv_nonneg.mpr hpk.le)
      (inv_nonneg.mpr (mul_pos hc hs).le)
  have hiid : (c * s)⁻¹ * (c * s)⁻¹ = c⁻¹ ^ 2 * s ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hs.le, Real.rpow_two]
    simp only [mul_inv, pow_two]
    ring
  have hpow : s ^ (1 - δ) * s ^ (-2 : ℝ) = s ^ (-1 - δ) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [hid, abs_mul, abs_neg, abs_mul, abs_inv, abs_inv,
    abs_of_pos hph, abs_of_pos hpk]
  calc
    |clockPerturbation s₀ h s - clockPerturbation s₀ k s| *
        ((sliceClock A s₀ κ h s)⁻¹ * (sliceClock A s₀ κ k s)⁻¹) ≤
      (P * s ^ (1 - δ)) * ((c * s)⁻¹ * (c * s)⁻¹) :=
      mul_le_mul hp hi
        (mul_nonneg (inv_nonneg.mpr hph.le) (inv_nonneg.mpr hpk.le))
        ((abs_nonneg _).trans hp)
    _ = (P * c⁻¹ ^ 2) * s ^ (-1 - δ) := by
      rw [hiid]
      calc
        P * s ^ (1 - δ) * (c⁻¹ ^ 2 * s ^ (-2 : ℝ)) =
          (P * c⁻¹ ^ 2) * (s ^ (1 - δ) * s ^ (-2 : ℝ)) := by ring
        _ = _ := by rw [hpow]

theorem sliceTail_path_abs_le
    {A s₀ κ δ P c : ℝ} {h k : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hc : 0 < c)
    (hih : IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀))
    (hik : IntegrableOn (sliceIntegrand A s₀ κ k) (Ioi s₀))
    (hqh : ∀ s ∈ Ioi s₀, c * s ≤ sliceClock A s₀ κ h s)
    (hqk : ∀ s ∈ Ioi s₀, c * s ≤ sliceClock A s₀ κ k s)
    (hp : ∀ s ∈ Ioi s₀,
      |clockPerturbation s₀ h s - clockPerturbation s₀ k s| ≤ P * s ^ (1 - δ)) :
    |sliceTail A s₀ κ h - sliceTail A s₀ κ k| ≤
      (P * c⁻¹ ^ 2) * (s₀ ^ (-δ) / δ) := by
  have hib := (integrableOn_Ioi_rpow_of_lt
    (show -1 - δ < -1 by linarith) hs₀).const_mul (P * c⁻¹ ^ 2)
  unfold sliceTail
  rw [← integral_sub hih hik]
  calc
    |∫ s in Ioi s₀, sliceIntegrand A s₀ κ h s - sliceIntegrand A s₀ κ k s| ≤
        ∫ s in Ioi s₀, |sliceIntegrand A s₀ κ h s - sliceIntegrand A s₀ κ k s| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioi s₀, (P * c⁻¹ ^ 2) * s ^ (-1 - δ) := by
      apply integral_mono_ae (hih.sub hik).abs hib
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact sliceIntegrand_path_abs_le (hs₀.trans hs) hc (hqh s hs) (hqk s hs) (hp s hs)
    _ = _ := by rw [integral_const_mul, integral_Ioi_rpow_neg_one_sub hs₀ hδ]

theorem sliceTail_path_abs_le_of_path
    {A s₀ κ δ H J D : ℝ} (h k : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hh : ContinuousOn h (Ici s₀)) (hk : ContinuousOn k (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (kbound : ∀ s : ℝ, s₀ ≤ s → |k s| ≤ J * s ^ (-δ))
    (hgap : ∀ s : ℝ, s₀ ≤ s → |h s - k s| ≤ D * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (ksmall : (4 * J / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    |sliceTail A s₀ κ h - sliceTail A s₀ κ k| ≤
      (16 * D / (A ^ 2 * δ * (1 - δ))) * s₀ ^ (-δ) := by
  have hb := sliceTail_path_abs_le hs₀ hδ (show 0 < A / 2 by positivity)
    (sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall hκ)
    (sliceTail_integrable_of_path k hA hs₀ hδ hδ1 hJ hk kbound ksmall hκ)
    (fun s hs => (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs.le).1)
    (fun s hs => (sliceClock_linear_bounds k hA hs₀ hδ hδ1 hJ kbound ksmall hκ hs.le).1)
    (fun s hs => clockPerturbation_sub_abs_le h k hh hk hs₀ hδ1 hD hgap hs.le)
  apply hb.trans_eq
  field_simp
  ring

/-- The exact manuscript path gain for synchronized parameters, established
from the actual clock integrals for both paths. -/
theorem synchronized_slice_parameter_stability
    {A s₀ κ η δ H J D : ℝ} (h k : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hh : ContinuousOn h (Ici s₀)) (hk : ContinuousOn k (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (kbound : ∀ s : ℝ, s₀ ≤ s → |k s| ≤ J * s ^ (-δ))
    (hgap : ∀ s : ℝ, s₀ ≤ s → |h s - k s| ≤ D * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (ksmall : (4 * J / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) (hη : |η| ≤ A * s₀ / 4)
    (hroot : sliceTail A s₀ κ h = 0) (kroot : sliceTail A s₀ η k = 0) :
    |κ - η| ≤ (64 * D / (δ * (1 - δ))) * s₀ ^ (1 - δ) := by
  have hm : 0 < (2 * A)⁻¹ ^ 2 * s₀⁻¹ := by positivity
  have hb := scalarInverse_root_stability
    (sliceTail_decrease_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall)
    (abs_le.mp hκ) (abs_le.mp hη) hroot kroot
    (fun x hx => sliceTail_path_abs_le_of_path h k hA hs₀ hδ hδ1 hH hJ hD
      hh hk hbound kbound hgap hsmall ksmall (abs_le.mpr hx))
  apply (mul_le_mul_iff_of_pos_left hm).mp
  apply hb.trans_eq
  rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add_one hs₀.ne']
  field_simp
  ring

theorem synchronizedSliceParameter_stability
    {A s₀ δ H J D : ℝ} (h k : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hh : ContinuousOn h (Ici s₀)) (hk : ContinuousOn k (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (kbound : ∀ s : ℝ, s₀ ≤ s → |k s| ≤ J * s ^ (-δ))
    (hgap : ∀ s : ℝ, s₀ ≤ s → |h s - k s| ≤ D * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32)
    (ksmall : (4 * J / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32) :
    |synchronizedSliceParameter A s₀ h - synchronizedSliceParameter A s₀ k| ≤
      (64 * D / (δ * (1 - δ))) * s₀ ^ (1 - δ) := by
  have hspec := synchronizedSliceParameter_spec h hA hs₀ hδ hδ1 hH hh hbound hsmall
  have kspec := synchronizedSliceParameter_spec k hA hs₀ hδ hδ1 hJ hk kbound ksmall
  exact synchronized_slice_parameter_stability h k hA hs₀ hδ hδ1 hH hJ hD
    hh hk hbound kbound hgap (hsmall.trans (by nlinarith)) (ksmall.trans (by nlinarith))
    hspec.1 kspec.1 hspec.2.1 kspec.2.1

/-- The size and path-difference estimate in the form stated in the paper. -/
theorem synchronizedSliceParameter_size_add_stability
    {A s₀ δ H J D : ℝ} (h k : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hh : ContinuousOn h (Ici s₀)) (hk : ContinuousOn k (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (kbound : ∀ s : ℝ, s₀ ≤ s → |k s| ≤ J * s ^ (-δ))
    (hgap : ∀ s : ℝ, s₀ ≤ s → |h s - k s| ≤ D * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32)
    (ksmall : (4 * J / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32) :
    |synchronizedSliceParameter A s₀ h| +
        |synchronizedSliceParameter A s₀ h - synchronizedSliceParameter A s₀ k| ≤
      (64 / (δ * (1 - δ))) * s₀ ^ (1 - δ) * (H + D) := by
  have hb := (synchronizedSliceParameter_spec h hA hs₀ hδ hδ1 hH hh hbound hsmall).2.2.1
  have hd := synchronizedSliceParameter_stability h k hA hs₀ hδ hδ1 hH hJ hD
    hh hk hbound kbound hgap hsmall ksmall
  calc
    _ ≤ (32 * H / (δ * (1 - δ))) * s₀ ^ (1 - δ) +
        (64 * D / (δ * (1 - δ))) * s₀ ^ (1 - δ) := add_le_add hb hd
    _ ≤ (64 * H / (δ * (1 - δ))) * s₀ ^ (1 - δ) +
        (64 * D / (δ * (1 - δ))) * s₀ ^ (1 - δ) := by
      gcongr
      norm_num
    _ = _ := by ring

end HBL.Kinematic
