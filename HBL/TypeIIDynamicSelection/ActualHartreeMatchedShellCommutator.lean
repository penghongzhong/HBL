import HBL.TypeIIDynamicSelection.ActualOneLayerSpatialOverlapGain
import Mathlib.Tactic

/-!
# The actual radial shell commutator for matched Cauchy data

The difference between an inner response and an outer propagation has
zero value and zero first derivative at their common interface.  Its
value and slope on the overlap are derived from the actual radial
Laplacian of that difference by two mean value estimates.  Applying the
original Hartree cutoff therefore costs a fixed multiple of the equation
defect, without an independent bound on the forced constant tail.

The bound on the equation defect is an explicit input to this local
lemma.  It is not a global residual estimate or a finite iteration step.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Zero Cauchy data at the actual interface control the mismatch by its
radial equation defect, with the physical powers R and R squared. -/
theorem actual_radial_matched_shell_zero_jet_bounds
    (d : ℝ → ℂ) (R A : ℝ) (hR : 0 < R) (hA : 0 ≤ A)
    (hd : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ d x)
    (hdd : ∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv d) x)
    (hleft : d R = 0) (hdleft : deriv d R = 0)
    (heq : ∀ x ∈ Icc R (2 * R), ‖complexRadialLaplacian d x‖ ≤ A) :
    ∀ r ∈ Icc R (2 * R),
      ‖d r‖ ≤ 4 * R ^ 2 * A ∧ ‖deriv d r‖ ≤ 4 * R * A := by
  let flux : ℝ → ℂ := fun x => (x : ℂ) ^ 2 * deriv d x
  have hstart : R ∈ Icc R (2 * R) := ⟨le_rfl, by linarith⟩
  have hflux (x : ℝ) (hx : x ∈ Icc R (2 * R)) :
      HasDerivAt flux ((x : ℂ) ^ 2 * complexRadialLaplacian d x) x := by
    have hxpos : 0 < x := hR.trans_le hx.1
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
    have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
        Complex.ofRealCLM.hasDerivAt (x := x)
    convert (hcast.pow 2).mul (hdd x hx).hasDerivAt using 1
    unfold complexRadialLaplacian
    push_cast
    field_simp [hxC]
    <;> ring
  have hfluxBound (x : ℝ) (hx : x ∈ Icc R (2 * R)) :
      ‖(x : ℂ) ^ 2 * complexRadialLaplacian d x‖ ≤ 4 * R ^ 2 * A := by
    have hxpos : 0 < x := hR.trans_le hx.1
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hxpos]
    calc
      x ^ 2 * ‖complexRadialLaplacian d x‖ ≤ x ^ 2 * A :=
        mul_le_mul_of_nonneg_left (heq x hx) (sq_nonneg x)
      _ ≤ (2 * R) ^ 2 * A :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hxpos.le hx.2 2) hA
      _ = 4 * R ^ 2 * A := by ring
  have hdist (r : ℝ) (hr : r ∈ Icc R (2 * R)) : ‖r - R‖ ≤ R := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr.1)]
    linarith [hr.2]
  have hslope (r : ℝ) (hr : r ∈ Icc R (2 * R)) :
      ‖deriv d r‖ ≤ 4 * R * A := by
    have hrpos : 0 < r := hR.trans_le hr.1
    have hm := (convex_Icc R (2 * R)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := flux) (f' := fun x => (x : ℂ) ^ 2 * complexRadialLaplacian d x)
      (C := 4 * R ^ 2 * A)
      (fun x hx => (hflux x hx).hasDerivWithinAt) hfluxBound hstart hr
    have hz : flux R = 0 := by simp [flux, hdleft]
    rw [hz, sub_zero] at hm
    have hf : r ^ 2 * ‖deriv d r‖ ≤ 4 * R ^ 3 * A := by
      calc
        _ = ‖flux r‖ := by
          simp [flux, norm_mul, norm_pow, abs_of_pos hrpos]
        _ ≤ (4 * R ^ 2 * A) * ‖r - R‖ := hm
        _ ≤ (4 * R ^ 2 * A) * R :=
          mul_le_mul_of_nonneg_left (hdist r hr) (by positivity)
        _ = 4 * R ^ 3 * A := by ring
    have hcancel : R ^ 2 * ‖deriv d r‖ ≤ R ^ 2 * (4 * R * A) := by
      calc
        _ ≤ r ^ 2 * ‖deriv d r‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hr.1 2) (norm_nonneg _)
        _ ≤ 4 * R ^ 3 * A := hf
        _ = R ^ 2 * (4 * R * A) := by ring
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).mp hcancel
  intro r hr
  refine ⟨?_, hslope r hr⟩
  have hm := (convex_Icc R (2 * R)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := d) (f' := deriv d) (C := 4 * R * A)
    (fun x hx => (hd x (hR.trans_le hx.1)).hasDerivAt.hasDerivWithinAt)
    hslope hstart hr
  rw [hleft, sub_zero] at hm
  calc
    ‖d r‖ ≤ (4 * R * A) * ‖r - R‖ := hm
    _ ≤ (4 * R * A) * R :=
      mul_le_mul_of_nonneg_left (hdist r hr) (by positivity)
    _ = 4 * R ^ 2 * A := by ring

private theorem actual_matched_shell_commutator_identity
    (d : ℝ → ℂ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hd : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ d x)
    (hdd : DifferentiableAt ℝ (deriv d) r) :
    complexRadialLaplacian (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
      actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r =
      2 * deriv (actualOneLayerInnerOverlapCutoff R) r * deriv d r +
      (deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
        (2 / (r : ℂ)) * deriv (actualOneLayerInnerOverlapCutoff R) r) * d r := by
  let chi := actualOneLayerInnerOverlapCutoff R
  have hc (x : ℝ) : DifferentiableAt ℝ chi x :=
    (actual_one_layer_overlap_cutoff_hasDerivAt R x).differentiableAt
  have hc2 : DifferentiableAt ℝ (deriv chi) r :=
    (actual_one_layer_overlap_cutoff_deriv_hasDerivAt R r hR.ne').differentiableAt
  have hfirst (x : ℝ) (hx : 0 < x) :
      deriv (fun t => chi t * d t) x = deriv chi x * d x + chi x * deriv d x :=
    ((hc x).hasDerivAt.mul (hd x hx).hasDerivAt).deriv
  have hnear : deriv (fun t => chi t * d t) =ᶠ[𝓝 r]
      (fun x => deriv chi x * d x + chi x * deriv d x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact hfirst x hx
  have hsecond : deriv (deriv (fun t => chi t * d t)) r =
      (deriv (deriv chi) r * d r + deriv chi r * deriv d r) +
      (deriv chi r * deriv d r + chi r * deriv (deriv d) r) := by
    exact (((hc2.hasDerivAt.mul (hd r hr).hasDerivAt).add
      ((hc r).hasDerivAt.mul hdd.hasDerivAt)).congr_of_eventuallyEq hnear).deriv
  change complexRadialLaplacian (fun x => chi x * d x) r -
      chi r * complexRadialLaplacian d r = _
  unfold complexRadialLaplacian
  rw [hsecond, hfirst r hr]
  dsimp only [chi]
  ring

/-- The original cutoff commutator is controlled by the actual equation
defect when the two profiles have matched Cauchy data.  Its constant is
fixed by the original smooth cutoff and is independent of R and d. -/
theorem actual_Hartree_matched_shell_cutoff_commutator :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℝ → ℂ) (R A : ℝ), 0 < R → 0 ≤ A →
        (∀ x : ℝ, 0 < x → DifferentiableAt ℝ d x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv d) x) →
        d R = 0 → deriv d R = 0 →
        (∀ x ∈ Icc R (2 * R), ‖complexRadialLaplacian d x‖ ≤ A) →
        ∀ r ∈ Icc R (2 * R),
          ‖complexRadialLaplacian
                (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
              actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r‖ ≤
            C * A := by
  obtain ⟨C1, C2, hC1, hC2, hcut⟩ :=
    actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  refine ⟨16 * C1 + 4 * C2, by positivity, ?_⟩
  intro d R A hR hA hd hdd hleft hdleft heq r hr
  have hrpos : 0 < r := hR.trans_le hr.1
  have hjet := actual_radial_matched_shell_zero_jet_bounds
    d R A hR hA hd hdd hleft hdleft heq r hr
  have hc := hcut R r hR
  have htwo : ‖2 / (r : ℂ)‖ ≤ 2 / R := by
    calc
      ‖2 / (r : ℂ)‖ = 2 / r := by simp [norm_div, abs_of_pos hrpos]
      _ ≤ 2 / R := actual_Hartree_radial_shell_two_over_r_le_two_over_R hR hr.1
  rw [actual_matched_shell_commutator_identity d R r hR hrpos hd (hdd r hr)]
  have hcoeff :
      ‖deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
        (2 / (r : ℂ)) * deriv (actualOneLayerInnerOverlapCutoff R) r‖ ≤
      C2 / R ^ 2 + (2 / R) * (C1 / R) := by
    calc
      _ ≤ ‖deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r‖ +
          ‖(2 / (r : ℂ)) * deriv (actualOneLayerInnerOverlapCutoff R) r‖ :=
        norm_add_le _ _
      _ ≤ C2 / R ^ 2 + (2 / R) * (C1 / R) := by
        rw [norm_mul]
        exact add_le_add hc.2 (mul_le_mul htwo hc.1 (norm_nonneg _) (by positivity))
  calc
    _ ≤ ‖2 * deriv (actualOneLayerInnerOverlapCutoff R) r * deriv d r‖ +
        ‖(deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
          (2 / (r : ℂ)) * deriv (actualOneLayerInnerOverlapCutoff R) r) * d r‖ :=
      norm_add_le _ _
    _ = 2 * ‖deriv (actualOneLayerInnerOverlapCutoff R) r‖ * ‖deriv d r‖ +
        ‖deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
          (2 / (r : ℂ)) * deriv (actualOneLayerInnerOverlapCutoff R) r‖ * ‖d r‖ := by
      simp only [norm_mul, norm_ofNat]
    _ ≤ 2 * (C1 / R) * (4 * R * A) +
        (C2 / R ^ 2 + (2 / R) * (C1 / R)) * (4 * R ^ 2 * A) := by
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hc.1 (by norm_num)) hjet.2
          (norm_nonneg _) (by positivity))
        (mul_le_mul hcoeff hjet.1 (norm_nonneg _) (by positivity))
    _ = (16 * C1 + 4 * C2) * A := by
      field_simp [hR.ne']
      <;> ring

/-- The weak first- and zero-order terms of an outer propagation can be
absorbed on the actual overlap. The mismatch is bounded through its own
equation and zero interface jet; no prior bound on that mismatch is used. -/
theorem actual_radial_matched_shell_weak_terms_absorption
    (d : ℝ → ℂ) (R A b : ℝ) (hR : 0 < R) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hsmall : 16 * R ^ 2 * b ≤ 1)
    (hd : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ d x)
    (hdd : ∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv d) x)
    (hleft : d R = 0) (hdleft : deriv d R = 0)
    (heq : ∀ x ∈ Icc R (2 * R),
      ‖complexRadialLaplacian d x‖ ≤ A + b * (‖d x‖ + R * ‖deriv d x‖)) :
    ∀ r ∈ Icc R (2 * R),
      ‖complexRadialLaplacian d r‖ ≤ 2 * A ∧
      ‖d r‖ ≤ 8 * R ^ 2 * A ∧ ‖deriv d r‖ ≤ 8 * R * A := by
  let Z : ℝ → ℝ := fun r => ‖d r‖ + R * ‖deriv d r‖
  have hZcont : ContinuousOn Z (Icc R (2 * R)) := by
    apply ContinuousOn.add
    · exact fun x hx => (hd x (hR.trans_le hx.1)).continuousAt.norm.continuousWithinAt
    · exact continuousOn_const.mul
        (fun x hx => (hdd x hx).continuousAt.norm.continuousWithinAt)
  obtain ⟨rmax, hrmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (show R ≤ 2 * R by linarith)) hZcont
  have hZnonneg : 0 ≤ Z rmax := by dsimp [Z]; positivity
  have hbound : ∀ x ∈ Icc R (2 * R),
      ‖complexRadialLaplacian d x‖ ≤ A + b * Z rmax := by
    intro x hx
    exact (heq x hx).trans (add_le_add_left
      (mul_le_mul_of_nonneg_left (hmax hx) hb) A)
  have hj := actual_radial_matched_shell_zero_jet_bounds
    d R (A + b * Z rmax) hR (by positivity) hd hdd hleft hdleft hbound
  have hmaxBound : Z rmax ≤ 8 * R ^ 2 * (A + b * Z rmax) := by
    calc
      _ ≤ 4 * R ^ 2 * (A + b * Z rmax) +
          R * (4 * R * (A + b * Z rmax)) :=
        add_le_add (hj rmax hrmax).1
          (mul_le_mul_of_nonneg_left (hj rmax hrmax).2 hR.le)
      _ = _ := by ring
  have hbudget : (16 * R ^ 2 * b) * Z rmax ≤ Z rmax := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsmall hZnonneg
  have hZ : Z rmax ≤ 16 * R ^ 2 * A := by nlinarith [hmaxBound, hbudget]
  have hbZ : b * Z rmax ≤ A := by
    calc
      _ ≤ b * (16 * R ^ 2 * A) := mul_le_mul_of_nonneg_left hZ hb
      _ = (16 * R ^ 2 * b) * A := by ring
      _ ≤ 1 * A := mul_le_mul_of_nonneg_right hsmall hA
      _ = A := one_mul A
  have hfinal : ∀ x ∈ Icc R (2 * R), ‖complexRadialLaplacian d x‖ ≤ 2 * A := by
    intro x hx
    exact (hbound x hx).trans (by linarith)
  have hjfinal := actual_radial_matched_shell_zero_jet_bounds
    d R (2 * A) hR (by positivity) hd hdd hleft hdleft hfinal
  intro r hr
  refine ⟨hfinal r hr, ?_, ?_⟩
  · exact (hjfinal r hr).1.trans_eq (by ring)
  · exact (hjfinal r hr).2.trans_eq (by ring)

end HBL.TypeIIDynamicSelection
