import HBL.MonopoleRadialLinearization
import HBL.MonopoleHartreeNonlinearBound
import HBL.AffineTailMinusZeroMode

/-! The actual truncated scalar radial static residual, with its differential,
Hartree, and local cubic terms on the same profile. This is a core estimate;
it does not assert spatial lifting, moving-cutoff dynamics, or outer matching. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- Differential linearity with genuine first and second derivatives. -/
theorem radialLaplacian_add_const_mul (f g : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hg : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x)
    {r : ℝ} (hr : 0 < r)
    (hf2 : DifferentiableAt ℝ (deriv f) r)
    (hg2 : DifferentiableAt ℝ (deriv g) r) :
    radialLaplacian (fun x => f x + c * g x) r =
      radialLaplacian f r + c * radialLaplacian g r := by
  have hfirst (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y => f y + c * g y) (deriv f x + c * deriv g x) x :=
    (hf x hx).hasDerivAt.add ((hg x hx).hasDerivAt.const_mul c)
  have he : deriv (fun x => f x + c * g x) =ᶠ[𝓝 r]
      (fun x => deriv f x + c * deriv g x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hfirst x hx).deriv
  have hsecond :=
    (hf2.hasDerivAt.add (hg2.hasDerivAt.const_mul c)).congr_of_eventuallyEq he
  unfold radialLaplacian
  rw [hsecond.deriv, (hfirst r hr).deriv]
  ring

/-- The bubble solves the actual radial Hartree stationary equation, using
the proved absolute-convergence normalization of its potential. -/
theorem bubble_radialHartree_stationary {r : ℝ} (hr : 0 < r) :
    radialLaplacian bubble r + radialHartreeNonlinearity bubble r = 0 := by
  have hq : ContDiff ℝ ∞ resonanceMinus := by
    change ContDiff ℝ ∞ (fun x : ℝ => x * bubble x)
    exact contDiff_id.mul bubble_contDiff_infty
  have hq1 := (contDiff_infty_iff_deriv.mp hq).1
  have hq2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hq).2).1
  have he : (fun x => resonanceMinus x / x) =ᶠ[𝓝 r] bubble := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    rw [resonanceMinus_def]
    have hx0 : 0 < x := hx
    field_simp [hx0.ne']
  have hLap : radialLaplacian bubble r = deriv (deriv resonanceMinus) r / r := by
    rw [← radialLaplacian_div_radius resonanceMinus (fun x _ => hq1 x) hr (hq2 r)]
    unfold radialLaplacian
    rw [he.deriv_eq, he.deriv.deriv_eq]
  have hV : potential r = 3 * bubble r ^ 4 := by
    unfold potential
    rw [show bubble r ^ 4 = (bubble r ^ 2) ^ 2 by ring, bubble_sq, inv_pow]
    ring
  have hzero := hMinus_resonanceMinus_zero r
  unfold hMinusApply at hzero
  rw [hV, resonanceMinus_def] at hzero
  rw [hLap, radialHartreeNonlinearity, radialHartreePotential_bubble_four hr]
  have hd : deriv (deriv resonanceMinus) r = -3 * bubble r ^ 4 * (r * bubble r) := by
    linarith
  rw [hd]
  field_simp [hr.ne']
  ring

/-- The static radial residual for the actual cutoff profile. -/
def monopoleRadialStaticResidual (R c r : ℝ) : ℝ :=
  radialLaplacian (monopolePerturbedRadialProfile R c) r +
    radialHartreeNonlinearity (monopolePerturbedRadialProfile R c) r +
    c * monopolePerturbedRadialProfile R c r ^ 3

/-- Exact same-object decomposition into the cutoff defect, actual Hartree
Taylor remainder, and local cubic perturbation. -/
theorem monopoleRadialStaticResidual_exact {R c r : ℝ} (hr : 0 < r) :
    monopoleRadialStaticResidual R c r =
      -(c * (hPlusApply (monopoleInnerProfile R) r - monopoleSource r) / r) +
      (radialHartreeNonlinearity (monopolePerturbedRadialProfile R c) r -
        radialHartreeNonlinearity bubble r - c * monopoleRadialHartreeFirstVariation R r) +
      (c * monopolePerturbedRadialProfile R c r ^ 3 - c * bubble r ^ 3) := by
  have hb1 := (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).1
  have hb2 := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2).1
  have hLap := radialLaplacian_add_const_mul bubble (monopoleInnerRadialProfile R) c
    (fun x _ => hb1 x) (fun _ hx => monopoleInnerRadialProfile_differentiableAt hx)
    hr (hb2 r) (monopoleInnerRadialProfile_deriv_differentiableAt hr)
  have hbase := bubble_radialHartree_stationary hr
  have hlin := monopoleRadial_linearization_eq_hPlus (R := R) hr
  unfold monopoleRadialStaticResidual
  change radialLaplacian (monopolePerturbedRadialProfile R c) r =
    radialLaplacian bubble r + c * radialLaplacian (monopoleInnerRadialProfile R) r at hLap
  rw [hLap]
  have heq : radialLaplacian (monopoleInnerRadialProfile R) r =
      -hPlusApply (monopoleInnerProfile R) r / r -
        monopoleRadialHartreeFirstVariation R r := by linarith
  have heq0 : radialLaplacian bubble r = -radialHartreeNonlinearity bubble r := by
    linarith
  rw [heq, heq0]
  unfold monopoleSource
  field_simp [hr.ne']
  ring

/-- A uniform amplitude-independent constant for the static core residual. -/
def monopoleStaticRadialBoundConstant : ℝ :=
  Real.pi * hartreeKappa * monopoleLinearGrowthConstant +
    monopoleHartreeNonlinearBoundConstant + monopoleLocalCubicBoundConstant

theorem monopoleStaticRadialBoundConstant_pos : 0 < monopoleStaticRadialBoundConstant := by
  have hM := monopoleLinearGrowthConstant_pos
  have hN := monopoleHartreeNonlinearBoundConstant_pos
  have hC := monopoleLocalCubicBoundConstant_pos
  unfold monopoleStaticRadialBoundConstant hartreeKappa
  positivity

/-- The actual cutoff static residual is uniformly quadratic on the core
0 < r <= R(c)/2, with R(c)=4/abs(c). Actual Hartree row integrability is
included, and no target equation or terminal bound is a hypothesis. -/
theorem monopoleRadialStaticResidual_core_quadratic_control {c r : ℝ}
    (hc : 0 < |c|) (hc1 : |c| ≤ 1) (hr : 0 < r)
    (hsep : r ≤ monopoleQuadraticRadius c / 2) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c rho ^ 4) (Ioi 0) ∧
    |monopoleRadialStaticResidual (monopoleQuadraticRadius c) c r| ≤
      monopoleStaticRadialBoundConstant * c ^ 2 := by
  have hN := monopoleRadialHartree_nonlinear_quadratic_control hc hc1 hr
  refine ⟨hN.1, ?_⟩
  have hcut := monopoleQuadraticRadius_core_defect hc hc1 hr hsep
  have hlocal := monopoleInnerRadialProfile_local_cubic_abs_le
    (R := monopoleQuadraticRadius c) hr hc1
  have hW : bubble r ^ 3 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (bubble r)) (bubble_abs_le_one r) 3
    have hb : 0 ≤ bubble r := by unfold bubble; positivity
    simpa only [one_pow, abs_of_nonneg hb] using h
  have hK : 0 ≤ Real.pi * hartreeKappa * monopoleLinearGrowthConstant * c ^ 2 := by
    have hM := monopoleLinearGrowthConstant_pos
    unfold hartreeKappa
    positivity
  have hcut' : |c * (hPlusApply (monopoleInnerProfile (monopoleQuadraticRadius c)) r -
      monopoleSource r) / r| ≤
      Real.pi * hartreeKappa * monopoleLinearGrowthConstant * c ^ 2 :=
    hcut.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hW hK)
  rw [monopoleRadialStaticResidual_exact hr]
  calc
    _ ≤ |c * (hPlusApply (monopoleInnerProfile (monopoleQuadraticRadius c)) r -
          monopoleSource r) / r| +
        |radialHartreeNonlinearity (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) r -
          radialHartreeNonlinearity bubble r -
          c * monopoleRadialHartreeFirstVariation (monopoleQuadraticRadius c) r| +
        |c * monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 -
          c * bubble r ^ 3| := by
      have tri (a b d : ℝ) : |a + b + d| ≤ |a| + |b| + |d| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      simpa only [abs_neg] using tri
        (-(c * (hPlusApply (monopoleInnerProfile (monopoleQuadraticRadius c)) r -
          monopoleSource r) / r))
        (radialHartreeNonlinearity (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c) r -
          radialHartreeNonlinearity bubble r -
          c * monopoleRadialHartreeFirstVariation (monopoleQuadraticRadius c) r)
        (c * monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r ^ 3 -
          c * bubble r ^ 3)
    _ ≤ (Real.pi * hartreeKappa * monopoleLinearGrowthConstant * c ^ 2) +
        monopoleHartreeNonlinearBoundConstant * c ^ 2 +
        monopoleLocalCubicBoundConstant * c ^ 2 := by
      exact add_le_add (add_le_add hcut' hN.2) hlocal
    _ = monopoleStaticRadialBoundConstant * c ^ 2 := by
      unfold monopoleStaticRadialBoundConstant
      ring

end HBL.Modulation.Monopole
