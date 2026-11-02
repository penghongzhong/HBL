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

end HBL.TypeIIDynamicSelection
