import HBL.KinematicPathBounds
import HBL.KinematicTailEstimates
import HBL.KinematicScalarInverse
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
The actual synchronized-slice parameter for a decaying continuous path.
Every analytic estimate is obtained from the path bound and the explicit
clock integral. In particular, continuity and decrease of the scalar tail
are conclusions, not assumptions on an abstract implicit function.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

theorem sliceTail_integrable_of_path
    {A s₀ κ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4)
    (hκ : |κ| ≤ A * s₀ / 4) :
    IntegrableOn (sliceIntegrand A s₀ κ h) (Ioi s₀) := by
  apply sliceIntegrand_integrableOn hA hs₀ hδ (show 0 < A / 2 by positivity)
    ((sliceClock_continuousOn A s₀ κ h hh).mono Ioi_subset_Ici_self)
  · intro s hs
    exact (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall hκ hs.le).1
  · intro s hs
    exact clockPerturbation_abs_le h hs₀ hδ1 hH hbound hs.le

theorem sliceTail_decrease_of_path
    {A s₀ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4) :
    ∀ κ ∈ Icc (-(A * s₀ / 4)) (A * s₀ / 4),
      ∀ η ∈ Icc (-(A * s₀ / 4)) (A * s₀ / 4), κ ≤ η →
        ((2 * A)⁻¹ ^ 2 * s₀⁻¹) * (η - κ) ≤
          sliceTail A s₀ κ h - sliceTail A s₀ η h := by
  intro κ hκ η hη hκη
  have habsκ : |κ| ≤ A * s₀ / 4 := abs_le.mpr hκ
  have habsη : |η| ≤ A * s₀ / 4 := abs_le.mpr hη
  have hb := sliceTail_parameter_bounds hs₀
    (show 0 < A / 2 by positivity) (show 0 < 2 * A by positivity) hκη
    (sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall habsη)
    (sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall habsκ)
    ((sliceClock_continuousOn A s₀ η h hh).mono Ioi_subset_Ici_self)
    ((sliceClock_continuousOn A s₀ κ h hh).mono Ioi_subset_Ici_self)
    (fun s hs => sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall habsη hs.le)
    (fun s hs => sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall habsκ hs.le)
  simpa only [mul_comm (η - κ)] using hb.1

theorem sliceTail_lipschitz_of_path
    {A s₀ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4) :
    ∀ κ ∈ Icc (-(A * s₀ / 4)) (A * s₀ / 4),
      ∀ η ∈ Icc (-(A * s₀ / 4)) (A * s₀ / 4),
        |sliceTail A s₀ κ h - sliceTail A s₀ η h| ≤
          ((A / 2)⁻¹ ^ 2 * s₀⁻¹) * |κ - η| := by
  intro κ hκ η hη
  have habsκ : |κ| ≤ A * s₀ / 4 := abs_le.mpr hκ
  have habsη : |η| ≤ A * s₀ / 4 := abs_le.mpr hη
  have hb := sliceTail_parameter_abs_le hs₀
    (show 0 < A / 2 by positivity) (show 0 < 2 * A by positivity)
    (sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall habsκ)
    (sliceTail_integrable_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall habsη)
    ((sliceClock_continuousOn A s₀ κ h hh).mono Ioi_subset_Ici_self)
    ((sliceClock_continuousOn A s₀ η h hh).mono Ioi_subset_Ici_self)
    (fun s hs => sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall habsκ hs.le)
    (fun s hs => sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall habsη hs.le)
  simpa only [mul_comm |κ - η|] using hb

theorem sliceTail_continuousOn_of_path
    {A s₀ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4) :
    ContinuousOn (fun κ => sliceTail A s₀ κ h)
      (Icc (-(A * s₀ / 4)) (A * s₀ / 4)) := by
  let L : NNReal := ⟨(A / 2)⁻¹ ^ 2 * s₀⁻¹, by positivity⟩
  have hLip : LipschitzOnWith L (fun κ => sliceTail A s₀ κ h)
      (Icc (-(A * s₀ / 4)) (A * s₀ / 4)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro κ hκ η hη
    change |sliceTail A s₀ κ h - sliceTail A s₀ η h| ≤
      ((A / 2)⁻¹ ^ 2 * s₀⁻¹) * |κ - η|
    exact sliceTail_lipschitz_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmall κ hκ η hη
  exact hLip.continuousOn

theorem sliceTail_zero_parameter_abs_le
    {A s₀ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4) :
    |sliceTail A s₀ 0 h| ≤
      (2 / (A ^ 2 * δ)) * ((4 * H / (1 - δ)) * s₀ ^ (-δ)) := by
  have hb := sliceTail_abs_le hA hs₀ hδ (show 0 < A / 2 by positivity)
    ((sliceClock_continuousOn A s₀ 0 h hh).mono Ioi_subset_Ici_self)
    (fun s hs => (sliceClock_linear_bounds h hA hs₀ hδ hδ1 hH hbound hsmall
      (show |(0 : ℝ)| ≤ A * s₀ / 4 by rw [abs_zero]; positivity) hs.le).1)
    (fun s hs => clockPerturbation_abs_le h hs₀ hδ1 hH hbound hs.le)
  calc
    |sliceTail A s₀ 0 h| ≤ (4 * H / (1 - δ)) / ((A / 2) * A) *
        (s₀ ^ (-δ) / δ) := by
      simpa only [abs_zero, zero_div, zero_mul, zero_add] using hb
    _ = _ := by field_simp

/-- A unique synchronized parameter for the actual decaying path, with the
explicit size required in the manuscript. -/
theorem existsUnique_synchronized_slice_parameter
    {A s₀ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32) :
    ∃ κ : ℝ, |κ| ≤ A * s₀ / 4 ∧ sliceTail A s₀ κ h = 0 ∧
      |κ| ≤ (32 * H / (δ * (1 - δ))) * s₀ ^ (1 - δ) ∧
      ∀ η : ℝ, |η| ≤ A * s₀ / 4 → sliceTail A s₀ η h = 0 → η = κ := by
  have hsmallq : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A / 4 :=
    hsmall.trans (by nlinarith)
  have hR : 0 < A * s₀ / 4 := by positivity
  have hm : 0 < (2 * A)⁻¹ ^ 2 * s₀⁻¹ := by positivity
  have hb := sliceTail_zero_parameter_abs_le h hA hs₀ hδ hδ1 hH hh hbound hsmallq
  have hFsmall : |sliceTail A s₀ 0 h| ≤
      ((2 * A)⁻¹ ^ 2 * s₀⁻¹) * (A * s₀ / 4) := by
    calc
      |sliceTail A s₀ 0 h| ≤
          (2 / (A ^ 2 * δ)) * ((4 * H / (1 - δ)) * s₀ ^ (-δ)) := hb
      _ ≤ (2 / (A ^ 2 * δ)) * (A * δ / 32) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by field_simp; ring
  obtain ⟨κ, hκ, hroot, hkbound, huniq⟩ :=
    scalarInverse_existsUnique_root_with_bound hR hm
      (sliceTail_continuousOn_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmallq)
      (sliceTail_decrease_of_path h hA hs₀ hδ hδ1 hH hh hbound hsmallq) hFsmall
  refine ⟨κ, abs_le.mpr hκ, hroot, ?_, ?_⟩
  · apply (mul_le_mul_iff_of_pos_left hm).mp
    apply hkbound.trans
    apply hb.trans_eq
    rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add_one hs₀.ne']
    field_simp
    ring
  · intro η hη hηroot
    exact huniq η (abs_le.mp hη) hηroot

/-- The synchronization selector depends on the actual path, not on a
particular witness for its decay norm. On the admissible class the root
exists and is unique; the default only totalizes the definition elsewhere. -/
def synchronizedSliceParameter (A s₀ : ℝ) (h : ℝ → ℝ) : ℝ := by
  classical
  exact if he : ∃ κ : ℝ, |κ| ≤ A * s₀ / 4 ∧ sliceTail A s₀ κ h = 0
    then Classical.choose he else 0

theorem synchronizedSliceParameter_spec
    {A s₀ δ H : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs₀ : 0 < s₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hH : 0 ≤ H) (hh : ContinuousOn h (Ici s₀))
    (hbound : ∀ s : ℝ, s₀ ≤ s → |h s| ≤ H * s ^ (-δ))
    (hsmall : (4 * H / (1 - δ)) * s₀ ^ (-δ) ≤ A * δ / 32) :
    |synchronizedSliceParameter A s₀ h| ≤ A * s₀ / 4 ∧
      sliceTail A s₀ (synchronizedSliceParameter A s₀ h) h = 0 ∧
      |synchronizedSliceParameter A s₀ h| ≤
        (32 * H / (δ * (1 - δ))) * s₀ ^ (1 - δ) ∧
      ∀ η : ℝ, |η| ≤ A * s₀ / 4 → sliceTail A s₀ η h = 0 →
        η = synchronizedSliceParameter A s₀ h := by
  classical
  obtain ⟨κ, hκ, hroot, hb, huniq⟩ :=
    existsUnique_synchronized_slice_parameter h hA hs₀ hδ hδ1 hH hh hbound hsmall
  have he : ∃ κ : ℝ, |κ| ≤ A * s₀ / 4 ∧ sliceTail A s₀ κ h = 0 :=
    ⟨κ, hκ, hroot⟩
  have hchoice := Classical.choose_spec he
  have hchoice_eq : Classical.choose he = κ := huniq _ hchoice.1 hchoice.2
  simp only [synchronizedSliceParameter, dite_eq_left he, hchoice_eq]
  exact ⟨hκ, hroot, hb, huniq⟩

end HBL.Kinematic
