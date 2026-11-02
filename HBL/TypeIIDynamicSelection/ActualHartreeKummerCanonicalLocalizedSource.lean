import HBL.TypeIIDynamicSelection.ActualHartreeKummerLocalizedCommutator
import HBL.TypeIIDynamicSelection.ActualKummerInnerCauchyMatch
import Mathlib.Tactic

/-!
# Original 2.12: normalized physical Kummer Green solution as LOCAL parametrix

Both genuine Kummer Wronskian endpoint normalizations already fix all
homogeneous coefficients. We preserve these conditions and localize
the ACTUAL normalized inhomogeneous Green solution (a=c=0) by the
original smooth moving overlap chi_R(r)=1-cutoff(r/R).

A genuine physical Kummer solution is differentiable only on its
positive annulus; global differentiability is NOT assumed. The
actual local C2 product rule gives, on every interior annulus point,

 L_K(chi_R u_K)-chi_R F
       =2chi_R' u_K' + (chi_R''+a_K(r)chi_R')u_K,

a_K(r)=2/r+i*r/2.

This is the exact canonical localized-parametrix PDE residual
that replaces an invalid claim of FREE inner/outer C1 matching.
The source/slope magnitude and moving interface remainders need
separate genuine weighted estimates before full original 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

/-- TRUE physical Kummer smooth-cutoff commutator using only
C1 regularity on a POSITIVE annulus around the evaluation point
(and a second local derivative), not an artificial globally smooth
extension of the original physical Kummer Green solution. -/
theorem actual_Hartree_Kummer_actual_cutoff_commutator_local
    (mu theta R : ℝ) (hR : R ≠ 0)
    (u : ℝ → ℂ) (a b r : ℝ)
    (hr : r ∈ Ioo a b)
    (hu : ∀ x ∈ Ioo a b, DifferentiableAt ℝ u x)
    (hu2 : DifferentiableAt ℝ (deriv u) r) :
    actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r -
      actualOneLayerInnerOverlapCutoff R r *
        actualHartreeFrozenKummerRadialApply mu theta u r =
      2 * deriv (actualOneLayerInnerOverlapCutoff R) r * deriv u r +
        (deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
          frozenFirstCoeff r *
            deriv (actualOneLayerInnerOverlapCutoff R) r) * u r := by
  let chi : ℝ → ℂ := actualOneLayerInnerOverlapCutoff R
  have hChi (x : ℝ) : DifferentiableAt ℝ chi x :=
    (actual_one_layer_overlap_cutoff_hasDerivAt R x).differentiableAt
  have hChi2 : DifferentiableAt ℝ (deriv chi) r :=
    (actual_one_layer_overlap_cutoff_deriv_hasDerivAt R r hR).differentiableAt
  have hFirstEventually :
      deriv (fun x => chi x * u x) =ᶠ[𝓝 r]
        (fun x => deriv chi x * u x + chi x * deriv u x) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact ((hChi x).hasDerivAt.mul (hu x hx).hasDerivAt).deriv
  have hFirst :
      deriv (fun x => chi x * u x) r =
        deriv chi r * u r + chi r * deriv u r :=
    ((hChi r).hasDerivAt.mul (hu r hr).hasDerivAt).deriv
  have hSecond :
      deriv (deriv (fun x => chi x * u x)) r =
        (deriv (deriv chi) r * u r + deriv chi r * deriv u r) +
          (deriv chi r * deriv u r + chi r * deriv (deriv u) r) := by
    have hModel :=
      ((hChi2.hasDerivAt.mul (hu r hr).hasDerivAt).add
        ((hChi r).hasDerivAt.mul hu2.hasDerivAt))
    exact (hModel.congr_of_eventuallyEq hFirstEventually).deriv
  change actualHartreeFrozenKummerRadialApply mu theta
      (fun x => chi x * u x) r -
    chi r * actualHartreeFrozenKummerRadialApply mu theta u r =
    2 * deriv chi r * deriv u r +
      (deriv (deriv chi) r + frozenFirstCoeff r * deriv chi r) * u r
  unfold actualHartreeFrozenKummerRadialApply
  rw [hSecond,hFirst]
  ring

/-- For the ORIGINAL homogeneous-coefficient-free normalized physical
Kummer Green solution, every interface cutoff error equals the
calculated PDE commutator, with no unproved outer C1 match. -/
theorem actual_Hartree_original_normalized_Kummer_localized_source_exact
    {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (R : ℝ) (hR : R ≠ 0)
    (r : ℝ) (hr : r ∈ Ioo (z - d) (z + d)) :
    let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
    actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r -
      actualOneLayerInnerOverlapCutoff R r * F r =
      2 * deriv (actualOneLayerInnerOverlapCutoff R) r * deriv u r +
        (deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
          frozenFirstCoeff r *
            deriv (actualOneLayerInnerOverlapCutoff R) r) * u r := by
  dsimp
  let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
  have hU (x : ℝ) (hx : x ∈ Ioo (z - d) (z + d)) :
      DifferentiableAt ℝ u x := by
    exact (actual_Kummer_Cauchy_corrected_classical_equation
      K d hd hde F hF 0 0 x (Ioo_subset_Icc_self hx)).1.differentiableAt
  have hU2 : DifferentiableAt ℝ (deriv u) r :=
    (actual_Kummer_Cauchy_corrected_classical_equation
      K d hd hde F hF 0 0 r (Ioo_subset_Icc_self hr)).2.1.differentiableAt
  have hODE : actualHartreeFrozenKummerRadialApply mu theta u r = F r := by
    exact (actual_Kummer_Cauchy_corrected_classical_equation
      K d hd hde F hF 0 0 r (Ioo_subset_Icc_self hr)).2.2
  have hComm := actual_Hartree_Kummer_actual_cutoff_commutator_local
    mu theta R hR u (z - d) (z + d) r hr hU hU2
  calc
    actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r -
      actualOneLayerInnerOverlapCutoff R r * F r =
      actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r -
      actualOneLayerInnerOverlapCutoff R r *
        actualHartreeFrozenKummerRadialApply mu theta u r := by rw [hODE]
    _ = 2 * deriv (actualOneLayerInnerOverlapCutoff R) r * deriv u r +
        (deriv (deriv (actualOneLayerInnerOverlapCutoff R)) r +
          frozenFirstCoeff r *
            deriv (actualOneLayerInnerOverlapCutoff R) r) * u r := hComm

/-- Quantitative error of the original homogeneous-free normalized Kummer
Green solution under the true moving cutoff. The constants are the already
constructed global smooth-cutoff C1/C2 bounds, not externally assumed source
orders. A moving-shell Green jet estimate is still needed for original 2.12. -/
theorem actual_Hartree_original_Kummer_green_cutoff_C2_bound
    {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (R : ℝ) (hR : 0 < R)
    (r : ℝ) (hr : r ∈ Ioo (z - d) (z + d)) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
      ‖actualHartreeFrozenKummerRadialApply mu theta
          (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r -
        actualOneLayerInnerOverlapCutoff R r * F r‖ ≤
        (2 * (C1 / R)) * ‖deriv u r‖ +
        (C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R)) *
          ‖u r‖ := by
  obtain ⟨C1, C2, hC1, hC2, hGlobal⟩ :=
    actual_Hartree_overlap_cutoff_uniform_C2_spatial_scaling
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  dsimp only
  let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
  let chi : ℝ → ℂ := actualOneLayerInnerOverlapCutoff R
  have hChi1 : ‖deriv chi r‖ ≤ C1 / R := (hGlobal R r hR).1
  have hChi2 : ‖deriv (deriv chi) r‖ ≤ C2 / R ^ 2 :=
    (hGlobal R r hR).2
  have hFirst :
      ‖(2 : ℂ) * deriv chi r * deriv u r‖ ≤
        (2 * (C1 / R)) * ‖deriv u r‖ := by
    calc
      _ = (2 * ‖deriv chi r‖) * ‖deriv u r‖ := by
        norm_num [norm_mul]
      _ ≤ (2 * (C1 / R)) * ‖deriv u r‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hChi1 (by norm_num))
          (norm_nonneg _)
  have hCoeff :
      ‖deriv (deriv chi) r + frozenFirstCoeff r * deriv chi r‖ ≤
        C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R) := by
    calc
      _ ≤ ‖deriv (deriv chi) r‖ +
          ‖frozenFirstCoeff r * deriv chi r‖ :=
        norm_add_le _ _
      _ = ‖deriv (deriv chi) r‖ +
          ‖frozenFirstCoeff r‖ * ‖deriv chi r‖ := by
        rw [norm_mul]
      _ ≤ C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R) :=
        add_le_add hChi2
          (mul_le_mul_of_nonneg_left hChi1 (norm_nonneg _))
  have hSecond :
      ‖(deriv (deriv chi) r +
          frozenFirstCoeff r * deriv chi r) * u r‖ ≤
        (C2 / R ^ 2 +
          ‖frozenFirstCoeff r‖ * (C1 / R)) * ‖u r‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)
  have hExact :
      actualHartreeFrozenKummerRadialApply mu theta
          (fun x => chi x * u x) r - chi r * F r =
        2 * deriv chi r * deriv u r +
          (deriv (deriv chi) r +
            frozenFirstCoeff r * deriv chi r) * u r :=
    actual_Hartree_original_normalized_Kummer_localized_source_exact
      K d hd hde F hF R hR.ne' r hr
  change ‖actualHartreeFrozenKummerRadialApply mu theta
      (fun x => chi x * u x) r - chi r * F r‖ ≤
    (2 * (C1 / R)) * ‖deriv u r‖ +
      (C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R)) *
        ‖u r‖
  rw [hExact]
  exact (norm_add_le _ _).trans (add_le_add hFirst hSecond)

/-- On the ACTUAL moving shell the large imaginary Kummer radial drift
is precisely compensated by one derivative of the physical cutoff.
This is elementary but prevents a false loss of one negative power
of the physical concentration scale. -/
theorem actual_Hartree_frozen_Kummer_shell_firstCoeff_bound
    {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) (hr2 : r ≤ 2 * R) :
    ‖frozenFirstCoeff r‖ ≤ 2 / R + R := by
  have hrpos : 0 < r := hR.trans_le hr
  have hA : ‖(2 : ℂ) / (r : ℂ)‖ = 2 / r := by
    rw [norm_div]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hB : ‖Complex.I * (r : ℂ) / 2‖ = r / 2 := by
    rw [norm_div, norm_mul]
    norm_num [Complex.norm_real, Complex.norm_I,
      Real.norm_eq_abs, abs_of_pos hrpos]
  have hLeft : (2 : ℝ) / r ≤ 2 / R :=
    actual_Hartree_radial_shell_two_over_r_le_two_over_R hR hr
  have hRight : r / 2 ≤ R := by linarith
  calc
    ‖frozenFirstCoeff r‖ ≤
        ‖(2 : ℂ) / (r : ℂ)‖ + ‖Complex.I * (r : ℂ) / 2‖ := by
      unfold frozenFirstCoeff
      exact norm_add_le _ _
    _ = 2 / r + r / 2 := by rw [hA, hB]
    _ ≤ 2 / R + R := add_le_add hLeft hRight

/-- Genuine localized normalized Kummer Green residual on the
physical moving shell. The size of the imaginary radial drift
is harmless: its R growth cancels the derivative's R inverse.
The ONLY remaining mathematical input for positive gain is a
uniform moving-shell estimate for the actual Green value and slope;
none is inserted into this theorem. -/
theorem actual_Hartree_normalized_Kummer_true_shell_cutoff_bound
    {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (R r : ℝ) (hR : 0 < R)
    (hr : r ∈ Ioo (z - d) (z + d))
    (hrlo : R ≤ r) (hrhi : r ≤ 2 * R) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
      ‖actualHartreeFrozenKummerRadialApply mu theta
          (fun x => actualOneLayerInnerOverlapCutoff R x * u x) r -
        actualOneLayerInnerOverlapCutoff R r * F r‖ ≤
        (2 * (C1 / R)) * ‖deriv u r‖ +
        (C1 + (C2 + 2 * C1) / R ^ 2) * ‖u r‖ := by
  obtain ⟨C1, C2, hC1, hC2, hOld⟩ :=
    actual_Hartree_original_Kummer_green_cutoff_C2_bound
      K d hd hde F hF R hR r hr
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  dsimp only at hOld ⊢
  let u : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
  have hOne : 0 ≤ C1 / R := div_nonneg hC1.le hR.le
  have hCoeff := actual_Hartree_frozen_Kummer_shell_firstCoeff_bound
    hR hrlo hrhi
  have hCoeffGain :
      C2 / R ^ 2 + ‖frozenFirstCoeff r‖ * (C1 / R) ≤
        C1 + (C2 + 2 * C1) / R ^ 2 := by
    have hMul :
        ‖frozenFirstCoeff r‖ * (C1 / R) ≤
          (2 / R + R) * (C1 / R) :=
      mul_le_mul_of_nonneg_right hCoeff hOne
    calc
      _ ≤ C2 / R ^ 2 + (2 / R + R) * (C1 / R) :=
        add_le_add le_rfl hMul
      _ = C1 + (C2 + 2 * C1) / R ^ 2 := by
        field_simp [hR.ne']
        <;> ring
  exact hOld.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hCoeffGain (norm_nonneg (u r))))

end HBL.TypeIIDynamicSelection
