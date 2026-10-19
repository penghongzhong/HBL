import HBL.MonopoleMovingCutoffSpatial
import Mathlib.Analysis.Complex.RealDeriv

/-! The complex radial residual of the actual real cutoff profile.  The
effective local cubic potential is kept explicit: the original Hartree
equation does not contain it.  These identities do not construct radiation
or identify scalar radial expressions with three-dimensional operators. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The positive-radius complex radial differential expression. -/
def complexRadialLaplacian (v : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv v) r + (2 / (r : ℂ)) * deriv v r

/-- The complex radial scaling generator, with actual spatial derivative. -/
def complexRadialDilation (v : ℝ → ℂ) (r : ℝ) : ℂ :=
  v r / 2 + (r : ℂ) * deriv v r

/-- The scalar radial Hartree potential already contains the coupling. -/
def complexRadialHartreeNonlinearity (v : ℝ → ℂ) (r : ℝ) : ℂ :=
  (radialHartreePotential (fun rho => ‖v rho‖ ^ 4) r : ℂ) *
    (‖v r‖ ^ 2 : ℝ) * v r

/-- The original complex radial renormalized residual, with no added slow
potential. Here omega has the manuscript convention minus the phase velocity. -/
def complexRadialRenormalizedResidual (V : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  Complex.I * deriv (fun t => V t r) s + complexRadialLaplacian (V s) r +
    complexRadialHartreeNonlinearity (V s) r +
    Complex.I * (b : ℂ) * complexRadialDilation (V s) r + (omega : ℂ) * V s r

/-- Real embedding preserves the actual modulus-based nonlinearity. -/
theorem complexRadialHartreeNonlinearity_ofReal (u : ℝ → ℝ) (r : ℝ) :
    complexRadialHartreeNonlinearity (fun x => (u x : ℂ)) r =
      (radialHartreeNonlinearity u r : ℂ) := by
  have hfour (x : ℝ) : |x| ^ 4 = x ^ 4 := by
    exact (show Even (4 : ℕ) from ⟨2, rfl⟩).pow_abs _
  simp only [complexRadialHartreeNonlinearity, Complex.norm_real,
    Real.norm_eq_abs, hfour, sq_abs, radialHartreeNonlinearity, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

/-- Embedding of the radial generator uses differentiability, so the
totalized derivative is not manipulated without its analytic hypothesis. -/
theorem complexRadialDilation_ofReal {u : ℝ → ℝ} {r : ℝ}
    (hu : DifferentiableAt ℝ u r) :
    complexRadialDilation (fun x => (u x : ℂ)) r =
      (dilationGenerator u r : ℂ) := by
  rw [complexRadialDilation, hu.hasDerivAt.ofReal_comp.deriv]
  simp only [dilationGenerator, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_mul]

/-- The second complex derivative is justified on a genuine positive-radius
neighborhood before identifying the real radial Laplacian. -/
theorem complexRadialLaplacian_ofReal (u : ℝ → ℝ)
    (hu : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ u x)
    {r : ℝ} (hr : 0 < r) (hu2 : DifferentiableAt ℝ (deriv u) r) :
    complexRadialLaplacian (fun x => (u x : ℂ)) r =
      (radialLaplacian u r : ℂ) := by
  have he : deriv (fun x => (u x : ℂ)) =ᶠ[𝓝 r]
      (fun x => ((deriv u x : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hu x hx).hasDerivAt.ofReal_comp.deriv
  have hsecond := hu2.hasDerivAt.ofReal_comp.congr_of_eventuallyEq he
  rw [complexRadialLaplacian, hsecond.deriv, (hu r hr).hasDerivAt.ofReal_comp.deriv]
  simp only [radialLaplacian, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_mul]

/-- Spatial first regularity of the same cutoff profile as in the actual
Hartree integral and static residual. -/
theorem monopolePerturbedRadialProfile_differentiableAt {R c r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (monopolePerturbedRadialProfile R c) r := by
  exact ((contDiff_infty_iff_deriv.mp bubble_contDiff_infty).1 r).add
    ((monopoleInnerRadialProfile_differentiableAt hr).const_mul c)

/-- Spatial second regularity of the actual cutoff profile. -/
theorem monopolePerturbedRadialProfile_deriv_differentiableAt
    {R c r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (deriv (monopolePerturbedRadialProfile R c)) r := by
  have hb := (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).1
  have hb2 := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2).1
  have he : deriv (monopolePerturbedRadialProfile R c) =ᶠ[𝓝 r]
      (fun x => deriv bubble x + c * deriv (monopoleInnerRadialProfile R) x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact ((hb x).hasDerivAt.add
      ((monopoleInnerRadialProfile_differentiableAt hx).hasDerivAt.const_mul c)).deriv
  have hmodel := (hb2 r).hasDerivAt.add
    ((monopoleInnerRadialProfile_deriv_differentiableAt (R := R) hr).hasDerivAt.const_mul c)
  exact (hmodel.congr_of_eventuallyEq he).differentiableAt

/-- Exact effective increment for the actual moving profile, including a
zero amplitude. The additional cubic term is displayed on the left and the
time-cutoff term is retained on the right; no radiation equation is assumed. -/
theorem monopoleComplexRadial_effective_increment {c : ℝ → ℝ} {cs s r : ℝ}
    (hc : HasDerivAt c cs s) (hr : 0 < r) (b omega : ℝ) :
    complexRadialRenormalizedResidual
        (fun t x => (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c t)) (c t) x : ℂ)) b omega s r +
      (c s : ℂ) *
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s) r : ℂ) ^ 3 -
      complexRadialRenormalizedResidual (fun _ x => (bubble x : ℂ)) b omega s r =
      (monopoleRadialStaticResidual (monopoleQuadraticRadius (c s)) (c s) r : ℂ) +
      Complex.I * (cs * monopoleRadialProfile r *
        (1 - cutoff (|c s| * r / 4) -
          (|c s| * r / 4) * deriv cutoff (|c s| * r / 4)) : ℝ) +
      Complex.I * (b : ℂ) *
        ((dilationGenerator (monopolePerturbedRadialProfile
          (monopoleQuadraticRadius (c s)) (c s)) r - dilationGenerator bubble r : ℝ) : ℂ) +
      (omega : ℂ) *
        ((monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s) r -
          bubble r : ℝ) : ℂ) := by
  have hb := (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).1
  have hb2 := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2).1
  have htime := (monopoleMovingCutoffTime_hasDerivAt hc r).ofReal_comp.deriv
  simp only [complexRadialRenormalizedResidual, htime, deriv_const,
    complexRadialHartreeNonlinearity_ofReal,
    complexRadialLaplacian_ofReal _ (fun _ hx =>
      monopolePerturbedRadialProfile_differentiableAt hx) hr
        (monopolePerturbedRadialProfile_deriv_differentiableAt hr),
    complexRadialLaplacian_ofReal bubble (fun x _ => hb x) hr (hb2 r),
    complexRadialDilation_ofReal (monopolePerturbedRadialProfile_differentiableAt hr),
    complexRadialDilation_ofReal (hb r)]
  have hzero : (radialLaplacian bubble r : ℂ) +
      (radialHartreeNonlinearity bubble r : ℂ) = 0 := by
    exact_mod_cast bubble_radialHartree_stationary hr
  simp only [monopoleRadialStaticResidual, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub]
  linear_combination -hzero

/-- The effective increment is an explicit difference of actual residuals;
its added constant cubic potential is part of this definition. -/
def monopoleComplexEffectiveIncrement (c : ℝ → ℝ) (b omega s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
      (fun t x => (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c t)) (c t) x : ℂ)) b omega s r +
    (c s : ℂ) *
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s) r : ℂ) ^ 3 -
    complexRadialRenormalizedResidual (fun _ x => (bubble x : ℂ)) b omega s r

/-- The three explicit first-order terms in the scalar radial core. -/
def monopoleComplexCoreFirstOrder (c cs b omega r : ℝ) : ℂ :=
  Complex.I * (cs * monopoleRadialProfile r : ℝ) +
    Complex.I * (b * c * dilationGenerator monopoleRadialProfile r : ℝ) +
    (omega * c * monopoleRadialProfile r : ℝ)

/-- The genuine static integral and quadratic estimate also hold at zero
amplitude. The product form of the core condition avoids division by c. -/
theorem monopoleRadialStaticResidual_core_quadratic_control_all {c r : ℝ}
    (hc1 : |c| ≤ 1) (hr : 0 < r) (hcore : |c| * r / 4 ≤ 1 / 2) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c rho ^ 4) (Ioi 0) ∧
    |monopoleRadialStaticResidual (monopoleQuadraticRadius c) c r| ≤
      monopoleStaticRadialBoundConstant * c ^ 2 := by
  by_cases hc : c = 0
  · subst c
    have he : monopolePerturbedRadialProfile (monopoleQuadraticRadius 0) 0 = bubble := by
      funext x
      simp only [monopolePerturbedRadialProfile, zero_mul, add_zero]
    rw [he]
    refine ⟨radialHartreeBubble_four_integrable hr, ?_⟩
    norm_num [monopoleRadialStaticResidual, he, bubble_radialHartree_stationary hr]
  · have hcp : 0 < |c| := abs_pos.mpr hc
    have hsep : r ≤ monopoleQuadraticRadius c / 2 := by
      unfold monopoleQuadraticRadius
      field_simp [hcp.ne'] at hcore ⊢
      nlinarith
    exact monopoleRadialStaticResidual_core_quadratic_control hcp hc1 hr hsep

/-- Exact dynamic core formula for the actual cutoff path, with every
first-order term and the same static residual, including zero crossings. -/
theorem monopoleComplexEffectiveIncrement_core_eq {c : ℝ → ℝ} {cs s r : ℝ}
    (hc : HasDerivAt c cs s) (hr : 0 < r) (hcore : |c s| * r / 4 < 1)
    (b omega : ℝ) :
    monopoleComplexEffectiveIncrement c b omega s r =
      (monopoleRadialStaticResidual (monopoleQuadraticRadius (c s)) (c s) r : ℂ) +
        monopoleComplexCoreFirstOrder (c s) cs b omega r := by
  have hvalue : monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s) r -
      bubble r = c s * monopoleRadialProfile r := by
    rw [monopoleMovingCutoffProfile_eq, cutoff_zero_of_le_one _ hcore.le]
    ring
  rw [monopoleComplexEffectiveIncrement,
    monopoleComplexRadial_effective_increment hc hr b omega,
    monopoleMovingCutoff_dilation_core_eq (c s) hr hcore, hvalue,
    cutoff_zero_of_le_one _ hcore.le, cutoff_deriv_zero_of_lt_one hcore]
  simp only [monopoleComplexCoreFirstOrder, mul_zero, sub_zero, mul_one,
    Complex.ofReal_mul]
  ring

/-- A complex-norm quadratic error estimate for the same actual core
residual. Absolute convergence of its full Hartree row is included. -/
theorem monopoleComplexEffectiveIncrement_core_quadratic_control
    {c : ℝ → ℝ} {cs s r : ℝ} (hc : HasDerivAt c cs s)
    (hc1 : |c s| ≤ 1) (hr : 0 < r) (hcore : |c s| * r / 4 ≤ 1 / 2)
    (b omega : ℝ) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s) rho ^ 4) (Ioi 0) ∧
    ‖monopoleComplexEffectiveIncrement c b omega s r -
      monopoleComplexCoreFirstOrder (c s) cs b omega r‖ ≤
        monopoleStaticRadialBoundConstant * (c s) ^ 2 := by
  have hstatic := monopoleRadialStaticResidual_core_quadratic_control_all hc1 hr hcore
  refine ⟨hstatic.1, ?_⟩
  rw [monopoleComplexEffectiveIncrement_core_eq hc hr (by linarith) b omega,
    add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs]
  exact hstatic.2

/-- The effective dynamic core residual is controlled by the actual
quadratic, amplitude-velocity, scaling, and phase orders. The constant is
independent of the path and radius; no evolution law is supplied as a premise. -/
theorem monopoleComplexEffectiveIncrement_core_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (c : ℝ → ℝ) (cs s r b omega : ℝ),
      HasDerivAt c cs s → |c s| ≤ 1 → 0 < r → |c s| * r / 4 ≤ 1 / 2 →
      ‖monopoleComplexEffectiveIncrement c b omega s r‖ ≤
        monopoleStaticRadialBoundConstant * (c s) ^ 2 +
        monopoleRadialBoundConstant * |cs| + D * |b * c s| +
        monopoleRadialBoundConstant * |omega * c s| := by
  obtain ⟨D, hDpos, hD⟩ := monopoleRadialProfile_dilation_bounded
  refine ⟨D, hDpos, ?_⟩
  intro c cs s r b omega hc hc1 hr hcore
  have hbound (a : ℝ) : |a * monopoleRadialProfile r| ≤
      monopoleRadialBoundConstant * |a| := by
    rw [abs_mul, mul_comm monopoleRadialBoundConstant]
    exact mul_le_mul_of_nonneg_left (monopoleRadialProfile_abs_le hr) (abs_nonneg a)
  have hdil : |b * c s * dilationGenerator monopoleRadialProfile r| ≤ D * |b * c s| := by
    rw [abs_mul, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hD r hr) (abs_nonneg (b * c s))
  have hfirst : ‖monopoleComplexCoreFirstOrder (c s) cs b omega r‖ ≤
      monopoleRadialBoundConstant * |cs| + D * |b * c s| +
        monopoleRadialBoundConstant * |omega * c s| := by
    unfold monopoleComplexCoreFirstOrder
    calc
      _ ≤ ‖Complex.I * (cs * monopoleRadialProfile r : ℝ)‖ +
          ‖Complex.I * (b * c s * dilationGenerator monopoleRadialProfile r : ℝ)‖ +
          ‖((omega * c s * monopoleRadialProfile r : ℝ) : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        simpa only [abs_mul] using add_le_add (add_le_add (hbound cs) hdil) (hbound (omega * c s))
  rw [monopoleComplexEffectiveIncrement_core_eq hc hr (by linarith) b omega]
  calc
    _ ≤ ‖(monopoleRadialStaticResidual (monopoleQuadraticRadius (c s)) (c s) r : ℂ)‖ +
        ‖monopoleComplexCoreFirstOrder (c s) cs b omega r‖ := norm_add_le _ _
    _ ≤ monopoleStaticRadialBoundConstant * (c s) ^ 2 +
        (monopoleRadialBoundConstant * |cs| + D * |b * c s| +
          monopoleRadialBoundConstant * |omega * c s|) := by
      apply add_le_add _ hfirst
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (monopoleRadialStaticResidual_core_quadratic_control_all hc1 hr hcore).2
    _ = _ := by ring

end HBL.Modulation.Monopole
