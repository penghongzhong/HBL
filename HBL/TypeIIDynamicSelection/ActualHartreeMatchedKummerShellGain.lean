import HBL.TypeIIDynamicSelection.ActualHartreeMatchedShellCommutator
import HBL.KummerFrozenAnnulus
import Mathlib.Tactic

/-!
# Actual scaled Kummer defects control matched shell cutoffs

The operator below is the full frozen Kummer operator in the inner
radius r=a*z.  Its first- and zero-order terms remain in the equation.
For a mismatch with zero Cauchy data at the interface, a small R/a
ratio allows those terms to be absorbed using the actual radial
equation.  The resulting cutoff commutator is bounded by a fixed
multiple of the Kummer defect itself.

The Kummer defect bound is an explicit input.  No bound on the radial
Laplacian, mismatch size or forced affine tail is assumed in its place.
This is a local shell estimate, not a finite-profile construction.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Profile.Kummer

/-- The complete frozen Kummer operator after the change r=a*z. -/
def actualMatchedScaledKummerApply
    (mu theta a : ℝ) (d : ℝ → ℂ) (r : ℝ) : ℂ :=
  complexRadialLaplacian d r +
    ((a ^ 2)⁻¹ : ℝ) •
      (Complex.I * (r : ℂ) / 2 * deriv d r +
        frozenZeroCoeff mu theta * d r)

private theorem actual_matched_scaled_Kummer_weak_equation
    (mu theta a : ℝ) (d : ℝ → ℂ) (R A r : ℝ)
    (ha : 0 < a) (hR : 0 < R) (hr : r ∈ Icc R (2 * R))
    (heq : ‖actualMatchedScaledKummerApply mu theta a d r‖ ≤ A) :
    ‖complexRadialLaplacian d r‖ ≤
      A + ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) *
        (‖d r‖ + R * ‖deriv d r‖) := by
  have hrpos : 0 < r := hR.trans_le hr.1
  have hq : 0 ≤ (a ^ 2)⁻¹ := inv_nonneg.mpr (pow_pos ha 2).le
  have hdrift :
      ‖Complex.I * (r : ℂ) / 2 * deriv d r +
        frozenZeroCoeff mu theta * d r‖ ≤
      (1 + ‖frozenZeroCoeff mu theta‖) * (‖d r‖ + R * ‖deriv d r‖) := by
    have hcoeff : ‖Complex.I * (r : ℂ) / 2‖ = r / 2 := by
      simp [abs_of_pos hrpos]
    calc
      _ ≤ ‖Complex.I * (r : ℂ) / 2 * deriv d r‖ +
          ‖frozenZeroCoeff mu theta * d r‖ := norm_add_le _ _
      _ = (r / 2) * ‖deriv d r‖ +
          ‖frozenZeroCoeff mu theta‖ * ‖d r‖ := by
        rw [norm_mul, norm_mul, hcoeff]
      _ ≤ R * ‖deriv d r‖ + ‖frozenZeroCoeff mu theta‖ * ‖d r‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (by linarith [hr.2]) (norm_nonneg _)) le_rfl
      _ ≤ (1 + ‖frozenZeroCoeff mu theta‖) *
          (‖d r‖ + R * ‖deriv d r‖) := by
        nlinarith [norm_nonneg (d r),
          mul_nonneg (norm_nonneg (frozenZeroCoeff mu theta))
            (mul_nonneg hR.le (norm_nonneg (deriv d r)))]
  have hsplit : complexRadialLaplacian d r =
      actualMatchedScaledKummerApply mu theta a d r -
        ((a ^ 2)⁻¹ : ℝ) •
          (Complex.I * (r : ℂ) / 2 * deriv d r +
            frozenZeroCoeff mu theta * d r) := by
    simp only [actualMatchedScaledKummerApply, add_sub_cancel_right]
  calc
    ‖complexRadialLaplacian d r‖ =
        ‖actualMatchedScaledKummerApply mu theta a d r -
          ((a ^ 2)⁻¹ : ℝ) •
            (Complex.I * (r : ℂ) / 2 * deriv d r +
              frozenZeroCoeff mu theta * d r)‖ := congrArg norm hsplit
    _ ≤ ‖actualMatchedScaledKummerApply mu theta a d r‖ +
        ‖((a ^ 2)⁻¹ : ℝ) •
          (Complex.I * (r : ℂ) / 2 * deriv d r +
            frozenZeroCoeff mu theta * d r)‖ := norm_sub_le _ _
    _ ≤ A + (a ^ 2)⁻¹ *
        ((1 + ‖frozenZeroCoeff mu theta‖) * (‖d r‖ + R * ‖deriv d r‖)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
      exact add_le_add heq (mul_le_mul_of_nonneg_left hdrift hq)
    _ = _ := by ring

/-- The genuine scaled Kummer defect, together with matched Cauchy
data, controls the original cutoff commutator uniformly.  The smallness
condition is the explicit weak-term budget on the actual shell. -/
theorem actual_Hartree_matched_scaled_Kummer_shell_gain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu theta a : ℝ) (d : ℝ → ℂ) (U : Set ℝ) (R A r0 : ℝ),
        IsOpen U → Icc R (2 * R) ⊆ U →
        0 < a → 0 < R → 0 ≤ A →
        16 * R ^ 2 * ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1 →
        r0 ∈ Icc R (2 * R) →
        (∀ x ∈ U, DifferentiableAt ℝ d x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv d) x) →
        d r0 = 0 → deriv d r0 = 0 →
        (∀ x ∈ Icc R (2 * R),
          ‖actualMatchedScaledKummerApply mu theta a d x‖ ≤ A) →
        ∀ r ∈ Icc R (2 * R),
          ‖complexRadialLaplacian d r‖ ≤ 2 * A ∧
          ‖d r‖ ≤ 8 * R ^ 2 * A ∧
          ‖deriv d r‖ ≤ 8 * R * A ∧
          ‖complexRadialLaplacian
                (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
              actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r‖ ≤
            C * A := by
  obtain ⟨C, hC, hcut⟩ := actual_Hartree_matched_shell_cutoff_commutator
  refine ⟨2 * C, by positivity, ?_⟩
  intro mu theta a d U R A r0 hU hSub ha hR hA hsmall hr0 hd hdd hleft hdleft heq
  have hb : 0 ≤ (1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2 := by positivity
  have hweak : ∀ x ∈ Icc R (2 * R),
      ‖complexRadialLaplacian d x‖ ≤
        A + ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) *
          (‖d x‖ + R * ‖deriv d x‖) := by
    intro x hx
    exact actual_matched_scaled_Kummer_weak_equation
      mu theta a d R A x ha hR hx (heq x hx)
  have hgain := actual_radial_matched_shell_weak_terms_absorption
    d R A ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) r0
      hR hA hb hsmall hr0 (fun x hx => hd x (hSub hx)) hdd hleft hdleft hweak
  intro r hr
  refine ⟨(hgain r hr).1, (hgain r hr).2.1, (hgain r hr).2.2, ?_⟩
  have hc := hcut d U R (2 * A) r0 hU hSub hR (by positivity) hr0 hd hdd hleft hdleft
    (fun x hx => (hgain x hx).1) r hr
  exact hc.trans_eq (by ring)

private theorem actual_matched_full_Kummer_commutator_identity
    (mu theta a : ℝ) (d : ℝ → ℂ) (R r : ℝ)
    (hd : DifferentiableAt ℝ d r) :
    actualMatchedScaledKummerApply mu theta a
        (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
      actualOneLayerInnerOverlapCutoff R r *
        actualMatchedScaledKummerApply mu theta a d r =
      (complexRadialLaplacian
          (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
        actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r) +
      ((a ^ 2)⁻¹ : ℝ) •
        (Complex.I * (r : ℂ) / 2 *
          deriv (actualOneLayerInnerOverlapCutoff R) r * d r) := by
  have hc : DifferentiableAt ℝ (actualOneLayerInnerOverlapCutoff R) r :=
    (actual_one_layer_overlap_cutoff_hasDerivAt R r).differentiableAt
  have hfirst :
      deriv (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r =
        deriv (actualOneLayerInnerOverlapCutoff R) r * d r +
          actualOneLayerInnerOverlapCutoff R r * deriv d r :=
    (hc.hasDerivAt.mul hd.hasDerivAt).deriv
  unfold actualMatchedScaledKummerApply
  rw [hfirst]
  simp only [Complex.real_smul]
  ring

/-- The full frozen Kummer commutator includes the transport derivative
of the cutoff. The same weak-term budget controls this additional term;
the zero-order coefficient commutes exactly with multiplication. -/
theorem actual_Hartree_matched_full_Kummer_shell_gain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu theta a : ℝ) (d : ℝ → ℂ) (U : Set ℝ) (R A r0 : ℝ),
        IsOpen U → Icc R (2 * R) ⊆ U →
        0 < a → 0 < R → 0 ≤ A →
        16 * R ^ 2 * ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1 →
        r0 ∈ Icc R (2 * R) →
        (∀ x ∈ U, DifferentiableAt ℝ d x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv d) x) →
        d r0 = 0 → deriv d r0 = 0 →
        (∀ x ∈ Icc R (2 * R),
          ‖actualMatchedScaledKummerApply mu theta a d x‖ ≤ A) →
        ∀ r ∈ Icc R (2 * R),
          ‖actualMatchedScaledKummerApply mu theta a
                (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
              actualOneLayerInnerOverlapCutoff R r *
                actualMatchedScaledKummerApply mu theta a d r‖ ≤ C * A := by
  obtain ⟨C0, hC0, hgain⟩ := actual_Hartree_matched_scaled_Kummer_shell_gain
  obtain ⟨C1, C2, hC1, _, hcut⟩ :=
    actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  refine ⟨C0 + 8 * C1, by positivity, ?_⟩
  intro mu theta a d U R A r0 hU hSub ha hR hA hsmall hr0 hd hdd hleft hdleft heq r hr
  have hrpos : 0 < r := hR.trans_le hr.1
  have hq : 0 ≤ (a ^ 2)⁻¹ := inv_nonneg.mpr (pow_pos ha 2).le
  have hjet := hgain mu theta a d U R A r0 hU hSub ha hR hA hsmall hr0
    hd hdd hleft hdleft heq r hr
  have hcutBound := (hcut R r hR).1
  have hratio : (a ^ 2)⁻¹ * R ^ 2 ≤ 1 := by
    have hfactor : 1 ≤ 16 * (1 + ‖frozenZeroCoeff mu theta‖) := by
      nlinarith [norm_nonneg (frozenZeroCoeff mu theta)]
    calc
      _ = 1 * (R ^ 2 / a ^ 2) := by ring
      _ ≤ (16 * (1 + ‖frozenZeroCoeff mu theta‖)) * (R ^ 2 / a ^ 2) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = 16 * R ^ 2 * ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) := by ring
      _ ≤ 1 := hsmall
  have hcoeff : ‖Complex.I * (r : ℂ) / 2‖ ≤ R := by
    have he : ‖Complex.I * (r : ℂ) / 2‖ = r / 2 := by
      simp [abs_of_pos hrpos]
    rw [he]
    linarith [hr.2]
  have hRc : R * (C1 / R) = C1 := by
    calc
      _ = (R / R) * C1 := by ring
      _ = C1 := by rw [div_self hR.ne', one_mul]
  have htransport :
      ‖((a ^ 2)⁻¹ : ℝ) •
        (Complex.I * (r : ℂ) / 2 *
          deriv (actualOneLayerInnerOverlapCutoff R) r * d r)‖ ≤
        8 * C1 * A := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq, norm_mul, norm_mul]
    calc
      _ ≤ (a ^ 2)⁻¹ * (R * (C1 / R) * (8 * R ^ 2 * A)) := by
        apply mul_le_mul_of_nonneg_left _ hq
        exact mul_le_mul
          (mul_le_mul hcoeff hcutBound (norm_nonneg _) hR.le)
          hjet.2.1 (norm_nonneg _) (by positivity)
      _ = (8 * C1 * A) * ((a ^ 2)⁻¹ * R ^ 2) := by rw [hRc]; ring
      _ ≤ (8 * C1 * A) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 8 * C1 * A := mul_one _
  rw [actual_matched_full_Kummer_commutator_identity
    mu theta a d R r (hd r (hSub hr))]
  calc
    _ ≤ ‖complexRadialLaplacian
            (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
          actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r‖ +
        ‖((a ^ 2)⁻¹ : ℝ) •
          (Complex.I * (r : ℂ) / 2 *
            deriv (actualOneLayerInnerOverlapCutoff R) r * d r)‖ := norm_add_le _ _
    _ ≤ C0 * A + 8 * C1 * A := add_le_add hjet.2.2.2 htransport
    _ = (C0 + 8 * C1) * A := by ring

end HBL.TypeIIDynamicSelection
