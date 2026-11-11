import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerShellGain
import Mathlib.Tactic

/-!
# Source-based parameter stability of the same zero-jet Kummer mismatch

A moving interface is first pulled back to a fixed annulus. Two ACTUAL
zero-jet fields can then be compared by subtracting their complete
Kummer equations. The only quantitative inputs below concern the
original operator sources; no separate value/slope envelope, derivative
of a chosen Kummer basis, third spatial jet, time order or rate is used.

This is an operator stability bridge. Producing the source-difference
bound for the selected four-piece nonlinear Hartree trajectory remains
an original mathematical obligation, not an assumption discharged here.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Profile.Kummer

private theorem kummer_difference_classical
    (mu theta a : ℝ) (u v : ℝ → ℂ) (U : Set ℝ) (hU : IsOpen U)
    (hu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hv : ∀ x ∈ U, DifferentiableAt ℝ v x)
    (r : ℝ) (hr : r ∈ U)
    (hu2 : DifferentiableAt ℝ (deriv u) r)
    (hv2 : DifferentiableAt ℝ (deriv v) r) :
    DifferentiableAt ℝ (deriv (fun x => u x - v x)) r ∧
      actualMatchedScaledKummerApply mu theta a (fun x => u x - v x) r =
        actualMatchedScaledKummerApply mu theta a u r -
          actualMatchedScaledKummerApply mu theta a v r := by
  have hfirst (x : ℝ) (hx : x ∈ U) :
      HasDerivAt (fun y => u y - v y) (deriv u x - deriv v x) x :=
    (hu x hx).hasDerivAt.sub (hv x hx).hasDerivAt
  have hnear : deriv (fun x => u x - v x) =ᶠ[𝓝 r]
      (fun x => deriv u x - deriv v x) := by
    filter_upwards [hU.mem_nhds hr] with x hx
    exact (hfirst x hx).deriv
  have hsecond := (hu2.hasDerivAt.sub hv2.hasDerivAt).congr_of_eventuallyEq hnear
  refine ⟨hsecond.differentiableAt, ?_⟩
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecond.deriv, (hfirst r hr).deriv]
  simp only [Complex.real_smul]
  ring

/-- Exact coefficient perturbation of the full scaled operator. The
radial Laplacian cancels, so no derivative of order three is introduced. -/
theorem actual_Kummer_parameter_difference_exact
    (mu1 theta1 a1 mu2 theta2 a2 : ℝ) (v : ℝ → ℂ) (r : ℝ) :
    actualMatchedScaledKummerApply mu1 theta1 a1 v r -
      actualMatchedScaledKummerApply mu2 theta2 a2 v r =
    (((a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹ : ℝ) •
      (Complex.I * (r : ℂ) / 2 * deriv v r)) +
    ((((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
        ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2) * v r) := by
  unfold actualMatchedScaledKummerApply
  simp only [Complex.real_smul, Complex.ofReal_sub]
  ring

private theorem kummer_parameter_difference_bound
    (mu1 theta1 a1 mu2 theta2 a2 R : ℝ) (v : ℝ → ℂ)
    (hR : 0 < R) (r : ℝ) (hr : r ∈ Icc R (2 * R)) :
    ‖actualMatchedScaledKummerApply mu1 theta1 a1 v r -
      actualMatchedScaledKummerApply mu2 theta2 a2 v r‖ ≤
      |(a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹| * R * ‖deriv v r‖ +
      ‖((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
        ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2‖ * ‖v r‖ := by
  have hrpos : 0 < r := hR.trans_le hr.1
  have hcoeff : ‖Complex.I * (r : ℂ) / 2‖ ≤ R := by
    have he : ‖Complex.I * (r : ℂ) / 2‖ = r / 2 := by
      simp [abs_of_pos hrpos]
    rw [he]
    linarith [hr.2]
  rw [actual_Kummer_parameter_difference_exact]
  calc
    _ ≤ ‖(((a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹ : ℝ) •
          (Complex.I * (r : ℂ) / 2 * deriv v r))‖ +
        ‖((((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
          ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2) * v r)‖ := norm_add_le _ _
    _ = |(a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹| *
          (‖Complex.I * (r : ℂ) / 2‖ * ‖deriv v r‖) +
        ‖((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
          ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2‖ * ‖v r‖ := by
      rw [norm_smul, Real.norm_eq_abs, norm_mul, norm_mul]
    _ ≤ _ := by
      refine add_le_add ?_ (le_refl _)
      calc
        _ ≤ |(a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹| * (R * ‖deriv v r‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)) (abs_nonneg _)
        _ = _ := by ring

/-- Fixed-domain source stability, including the actual cutoff Laplacian
commutator. The second field's value and slope are PRODUCED from its
operator source by the existing zero-Cauchy-jet absorption theorem.
A12 bounds the difference of the two actual complete operator sources.
The matching anchor can be the RIGHT endpoint; no re-selection is needed
merely to restrict the same Green solution to a backward overlap. -/
theorem actual_Kummer_fixed_domain_source_parameter_stability :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu1 theta1 a1 mu2 theta2 a2 R r0 A2 A12 : ℝ)
        (u v : ℝ → ℂ) (U : Set ℝ),
        IsOpen U → Icc R (2 * R) ⊆ U →
        0 < a1 → 0 < a2 → 0 < R → 0 ≤ A2 → 0 ≤ A12 →
        16 * R ^ 2 * ((1 + ‖frozenZeroCoeff mu1 theta1‖) / a1 ^ 2) ≤ 1 →
        16 * R ^ 2 * ((1 + ‖frozenZeroCoeff mu2 theta2‖) / a2 ^ 2) ≤ 1 →
        r0 ∈ Icc R (2 * R) →
        (∀ x ∈ U, DifferentiableAt ℝ u x) →
        (∀ x ∈ U, DifferentiableAt ℝ v x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv u) x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv v) x) →
        u r0 = 0 → deriv u r0 = 0 → v r0 = 0 → deriv v r0 = 0 →
        (∀ x ∈ Icc R (2 * R),
          ‖actualMatchedScaledKummerApply mu2 theta2 a2 v x‖ ≤ A2) →
        (∀ x ∈ Icc R (2 * R),
          ‖actualMatchedScaledKummerApply mu1 theta1 a1 u x -
            actualMatchedScaledKummerApply mu2 theta2 a2 v x‖ ≤ A12) →
        let Q := |(a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹| +
          ‖((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
            ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2‖
        let A := A12 + 8 * R ^ 2 * A2 * Q
        let d := fun x => u x - v x
        ∀ r ∈ Icc R (2 * R),
          ‖complexRadialLaplacian d r‖ ≤ 2 * A ∧
          ‖d r‖ ≤ 8 * R ^ 2 * A ∧
          ‖deriv d r‖ ≤ 8 * R * A ∧
          ‖complexRadialLaplacian
              (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
            actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r‖ ≤ C * A := by
  obtain ⟨C, hC, hgain⟩ := actual_Hartree_matched_scaled_Kummer_shell_gain
  refine ⟨C, hC, ?_⟩
  intro mu1 theta1 a1 mu2 theta2 a2 R r0 A2 A12 u v U
    hU hSub ha1 ha2 hR hA2 hA12 hsmall1 hsmall2 hr0 hu hv hu2 hv2
    hu0 hdu0 hv0 hdv0 hsource2 hsource12
  dsimp only
  let Q := |(a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹| +
    ‖((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
      ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2‖
  let A := A12 + 8 * R ^ 2 * A2 * Q
  let d := fun x => u x - v x
  have hA : 0 ≤ A := by dsimp [A, Q]; positivity
  have hbase := hgain mu2 theta2 a2 v U R A2 r0
    hU hSub ha2 hR hA2 hsmall2 hr0 hv hv2 hv0 hdv0 hsource2
  have hd (x : ℝ) (hx : x ∈ U) : DifferentiableAt ℝ d x :=
    (hu x hx).sub (hv x hx)
  have hd2 (x : ℝ) (hx : x ∈ Icc R (2 * R)) :
      DifferentiableAt ℝ (deriv d) x :=
    (kummer_difference_classical mu1 theta1 a1 u v U hU hu hv
      x (hSub hx) (hu2 x hx) (hv2 x hx)).1
  have hd0 : d r0 = 0 := by dsimp [d]; rw [hu0, hv0]; ring
  have hdd0 : deriv d r0 = 0 := by
    have h := (hu r0 (hSub hr0)).hasDerivAt.sub (hv r0 (hSub hr0)).hasDerivAt
    have he : deriv d r0 = deriv u r0 - deriv v r0 := h.deriv
    rw [he, hdu0, hdv0]
    ring
  have hsource (x : ℝ) (hx : x ∈ Icc R (2 * R)) :
      ‖actualMatchedScaledKummerApply mu1 theta1 a1 d x‖ ≤ A := by
    have hb := hbase x hx
    have hp := kummer_parameter_difference_bound
      mu1 theta1 a1 mu2 theta2 a2 R v hR x hx
    have hparam : ‖actualMatchedScaledKummerApply mu1 theta1 a1 v x -
        actualMatchedScaledKummerApply mu2 theta2 a2 v x‖ ≤ 8 * R ^ 2 * A2 * Q := by
      calc
        _ ≤ |(a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹| * R * ‖deriv v x‖ +
            ‖((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
              ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2‖ * ‖v x‖ := hp
        _ ≤ |(a1 ^ 2)⁻¹ - (a2 ^ 2)⁻¹| * R * (8 * R * A2) +
            ‖((a1 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu1 theta1 -
              ((a2 ^ 2)⁻¹ : ℝ) • frozenZeroCoeff mu2 theta2‖ * (8 * R ^ 2 * A2) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hb.2.2.1 (by positivity))
            (mul_le_mul_of_nonneg_left hb.2.1 (norm_nonneg _))
        _ = _ := by dsimp [Q]; ring
    have he := (kummer_difference_classical mu1 theta1 a1 u v U hU hu hv
      x (hSub hx) (hu2 x hx) (hv2 x hx)).2
    change ‖actualMatchedScaledKummerApply mu1 theta1 a1
      (fun y => u y - v y) x‖ ≤ A
    rw [he]
    calc
      _ = ‖(actualMatchedScaledKummerApply mu1 theta1 a1 u x -
              actualMatchedScaledKummerApply mu2 theta2 a2 v x) -
            (actualMatchedScaledKummerApply mu1 theta1 a1 v x -
              actualMatchedScaledKummerApply mu2 theta2 a2 v x)‖ := by congr 1; ring
      _ ≤ ‖actualMatchedScaledKummerApply mu1 theta1 a1 u x -
              actualMatchedScaledKummerApply mu2 theta2 a2 v x‖ +
            ‖actualMatchedScaledKummerApply mu1 theta1 a1 v x -
              actualMatchedScaledKummerApply mu2 theta2 a2 v x‖ := norm_sub_le _ _
      _ ≤ A12 + 8 * R ^ 2 * A2 * Q := add_le_add (hsource12 x hx) hparam
      _ = A := rfl
  exact hgain mu1 theta1 a1 d U R A r0 hU hSub ha1 hR hA
    hsmall1 hr0 hd hd2 hd0 hdd0 hsource


/-!
The two *physical* fields in the original matched overlap share a possibly
nonzero Fredholm Cauchy jet. When their frozen operator parameters agree,
their difference itself has zero jet. No harmonic subtraction and no
spurious assumption that either individual field vanishes is required.
This handles the same-time, same-operator piece only: parameter differences
and the actual full nonlinear residual time gain are separate obligations.
-/

/-- Genuine nonzero-matched-jet source-to-C¹ control. The individual fields
are not assumed zero at the matching radius. Only the difference of their
actual Kummer operator sources is bounded, and the zero initial data of
their DIFFERENCE are proved from their common Cauchy jet. -/
theorem actual_Kummer_same_parameter_nonzero_matched_jet_source_gain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu theta a R r0 A : ℝ)
        (u v : ℝ → ℂ) (U : Set ℝ),
        IsOpen U → Icc R (2 * R) ⊆ U →
        0 < a → 0 < R → 0 ≤ A →
        16 * R ^ 2 * ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1 →
        r0 ∈ Icc R (2 * R) →
        (∀ x ∈ U, DifferentiableAt ℝ u x) →
        (∀ x ∈ U, DifferentiableAt ℝ v x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv u) x) →
        (∀ x ∈ Icc R (2 * R), DifferentiableAt ℝ (deriv v) x) →
        u r0 = v r0 → deriv u r0 = deriv v r0 →
        (∀ x ∈ Icc R (2 * R),
          ‖actualMatchedScaledKummerApply mu theta a u x -
            actualMatchedScaledKummerApply mu theta a v x‖ ≤ A) →
        let d := fun x => u x - v x
        ∀ r ∈ Icc R (2 * R),
          ‖complexRadialLaplacian d r‖ ≤ 2 * A ∧
          ‖d r‖ ≤ 8 * R ^ 2 * A ∧
          ‖deriv d r‖ ≤ 8 * R * A ∧
          ‖complexRadialLaplacian
              (fun x => actualOneLayerInnerOverlapCutoff R x * d x) r -
            actualOneLayerInnerOverlapCutoff R r * complexRadialLaplacian d r‖ ≤
            C * A := by
  obtain ⟨C, hC, hgain⟩ := actual_Hartree_matched_scaled_Kummer_shell_gain
  refine ⟨C, hC, ?_⟩
  intro mu theta a R r0 A u v U hU hSub ha hR hA hsmall hr0
    hu hv hu2 hv2 hvalue hslope hsource
  dsimp only
  let d := fun x => u x - v x
  have hd (x : ℝ) (hx : x ∈ U) : DifferentiableAt ℝ d x :=
    (hu x hx).sub (hv x hx)
  have hd2 (x : ℝ) (hx : x ∈ Icc R (2 * R)) :
      DifferentiableAt ℝ (deriv d) x :=
    (kummer_difference_classical mu theta a u v U hU hu hv
      x (hSub hx) (hu2 x hx) (hv2 x hx)).1
  have hd0 : d r0 = 0 := by
    dsimp [d]
    rw [hvalue]
    ring
  have hdd0 : deriv d r0 = 0 := by
    have h := (hu r0 (hSub hr0)).hasDerivAt.sub (hv r0 (hSub hr0)).hasDerivAt
    have he : deriv d r0 = deriv u r0 - deriv v r0 := h.deriv
    rw [he, hslope]
    ring
  have hactual (x : ℝ) (hx : x ∈ Icc R (2 * R)) :
      ‖actualMatchedScaledKummerApply mu theta a d x‖ ≤ A := by
    rw [(kummer_difference_classical mu theta a u v U hU hu hv
      x (hSub hx) (hu2 x hx) (hv2 x hx)).2]
    exact hsource x hx
  exact hgain mu theta a d U R A r0 hU hSub ha hR hA hsmall
    hr0 hd hd2 hd0 hdd0 hactual

end HBL.TypeIIDynamicSelection
