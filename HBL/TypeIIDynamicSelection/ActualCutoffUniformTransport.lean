import HBL.TypeIIDynamicSelection.ActualMomentTransportGain
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Original smooth Hartree cutoff: a uniform, all-radii PDE transport gain

The fixed smooth cutoff chi from the original paper has its derivative
supported on [1,2], and one GLOBAL finite positive derivative bound.
Those are proved, not assumed as inputs about the cutoff.

For the actual Hartree 3D inverse-square radiation moment,
 c(s) = kappa_H ell(s) m0[z_g(t(s))],
the already strict-certified material derivative has size O(ell^2)
uniformly for every r>=0, WITHOUT assuming the observation point lies
in the cutoff annulus and WITHOUT passing a cutoff derivative bound
as an independent hypothesis.

The final theorem derives m0' from the original radial Hartree PDE
and Mathlib dominated differentiation. It does not assume or prescribe
a blowup exponent or the full Hartree modulation trapping window.
The actual regular radiation's PDE/dominated source inputs and the
positivity of its terminal moment remain explicit analytic obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The derivative of the ACTUAL fixed manuscript cutoff vanishes
outside its outer annulus boundary, by local constant equality. -/
theorem actual_fixed_cutoff_deriv_zero_of_gt_two
    {x : ℝ} (hx : 2 < x) : deriv cutoff x = 0 := by
  have he : cutoff =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact cutoff_one_of_two_le y hy.le
  rw [he.deriv_eq]
  exact deriv_const x 1

/-- The REAL manuscript cutoff has a universal positive C1 bound.
It depends on no modulation parameter, PDE solution or radius. -/
theorem exists_actual_fixed_cutoff_uniform_deriv_bound :
    ∃ Cχ : ℝ, 0 < Cχ ∧ ∀ x : ℝ, |deriv cutoff x| ≤ Cχ := by
  have hcont : Continuous (deriv cutoff) :=
    ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).2).continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).
      exists_bound_of_continuousOn hcont.continuousOn
  have hCnonneg : 0 ≤ C := by
    have hOne := hC 1 (show (1 : ℝ) ∈ Icc 1 2 by norm_num)
    exact (norm_nonneg (deriv cutoff 1)).trans hOne
  refine ⟨C + 1, by linarith, ?_⟩
  intro x
  by_cases hleft : x < 1
  · rw [cutoff_deriv_zero_of_lt_one hleft]
    simp only [abs_zero]
    linarith
  · by_cases hright : 2 < x
    · rw [actual_fixed_cutoff_deriv_zero_of_gt_two hright]
      simp only [abs_zero]
      linarith
    · have hx : x ∈ Icc (1 : ℝ) 2 :=
        ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      have hb := hC x hx
      rw [Real.norm_eq_abs] at hb
      linarith

/-- A UNIVERSAL spatial estimate for the manuscript moving cutoff:
the annulus restriction and cutoff-derivative bound have now been
proved from the actual fixed smooth chi, not left as hypotheses.
The physical 3D radiation moment is still an input C1 scalar here. -/
theorem actual_moment_cutoff_uniform_all_r_transport_gain
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s dm : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s))
    (hmpos : 0 < actualPhysicalInverseSquareMoment (z (time s))) :
    ∃ Cχ : ℝ, 0 < Cχ ∧
      ∀ r : ℝ, 0 ≤ r →
        |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
          b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
          (2 * (ell s) ^ 2 *
            (|dm| / radialPhysicalQuarticMoment (z (time s)))) * Cχ := by
  obtain ⟨Cχ, hCχpos, hCχ⟩ := exists_actual_fixed_cutoff_uniform_deriv_bound
  refine ⟨Cχ, hCχpos, ?_⟩
  intro r hr
  let c : ℝ := actualPhysicalRadiationMonopole ell z time s
  by_cases htrans : c * r / 4 ≤ 2
  · exact actualMomentInnerCutoff_transport_length_gain
      ell b z time r Cχ hEll hEllPos hTime
      hMoment hmpos hr htrans (hCχ _)
  · have hout : 2 < c * r / 4 := lt_of_not_ge htrans
    have hcut : deriv cutoff (c * r / 4) = 0 :=
      actual_fixed_cutoff_deriv_zero_of_gt_two hout
    have hmrad : HasDerivAt
        (fun t => radialPhysicalQuarticMoment (z t)) dm (time s) := by
      simpa only [actual_physical_inverse_square_radial_reduction] using hMoment
    have htransport := actualMomentInnerCutoff_material_derivative
      ell b z time r hEll hEllPos hTime hmrad
    have hmposRad : 0 < radialPhysicalQuarticMoment (z (time s)) := by
      simpa only [actual_physical_inverse_square_radial_reduction] using hmpos
    have hnonneg :
        0 ≤ (2 * (ell s) ^ 2 *
          (|dm| / radialPhysicalQuarticMoment (z (time s)))) * Cχ := by
      positivity
    change |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
      b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤ _
    rw [htransport, hcut, mul_zero, abs_zero]
    exact hnonneg

/-- ALL-RADII O(ell^2) moving cutoff source for the ACTUAL HARTREE PDE.
Neither differentiability of m0, the transition support, nor a cutoff
derivative bound is postulated in its theorem hypotheses. They are
derived from the real PDE, dominated differentiation, and the actual chi. -/
theorem actual_Hartree_PDE_cutoff_uniform_all_r_length_gain
    (ell b : ℝ → ℝ) (z zt : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    {s : ℝ}
    (hEll : HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (I : Set ℝ)
    (hI : I ∈ 𝓝 (time s))
    (hZmeas : ∀ᶠ t in 𝓝 (time s),
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (fun rho => ‖z (time s) rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho =>
        actualRadialQuarticMomentVelocity (z (time s) rho) (zt (time s) rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ (rho : ℝ), 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x : ℝ => (z x rho).im) (zt t rho).im t)
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt (time s) rho = Complex.I *
        (complexRadialLaplacian (z (time s)) rho +
          complexRadialHartreeNonlinearity (z (time s)) rho))
    (hmpos : 0 < actualPhysicalInverseSquareMoment (z (time s))) :
    ∃ Cχ : ℝ, 0 < Cχ ∧
      ∀ r : ℝ, 0 ≤ r →
        |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
          b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
          (2 * (ell s) ^ 2 *
            (|actualMomentLaplacianFlux (z (time s))| /
              radialPhysicalQuarticMoment (z (time s)))) * Cχ := by
  have hMoment : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t))
      (actualMomentLaplacianFlux (z (time s))) (time s) :=
    actual_physical_threeD_Hartree_radiation_moment_PDE_flux
      z zt (time s) I hI hZmeas hZint hVelMeas B hB hBound
      hRe hIm hPDE
  exact actual_moment_cutoff_uniform_all_r_transport_gain
    ell b z time hEll hEllPos hTime hMoment hmpos

end HBL.TypeIIDynamicSelection
