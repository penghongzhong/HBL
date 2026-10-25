import HBL.PhysicalRadial3Gradient
import HBL.WeightedVolterraAMinusKernel

/-!
Exact physical phase energy and coercivity on C1 radial profiles which
vanish beyond a finite radius. Half-line derivative L2 membership is
proved, not assumed. The global coordinate isometry is obtained by
reducing both integrals to the already proved finite-interval identity.
This closes the physical phase form on this core, not its Sobolev
completion or the nonlocal real-channel Hessian.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology RealInnerProductSpace ContDiff

namespace HBL.Modulation.Monopole
open HBL.L2Kernel HBL.Modulation.AffineTail

private theorem phaseCore_deriv_zero
    (f : ℝ → ℝ) {R r : ℝ}
    (hcut : ∀ t : ℝ, R ≤ t → f t = 0) (hr : R < r) :
    deriv f r = 0 := by
  have he : f =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact hcut t (le_of_lt ht)
  exact ((hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq he).deriv

private theorem phaseCore_U_deriv_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {R r : ℝ}
    (hcut : ∀ t : ℝ, R ≤ t → f t = 0) (hr : R < r) :
    deriv (radialU f) r = 0 := by
  rw [radialU_deriv f hf r, hcut r hr.le,
    phaseCore_deriv_zero f hcut hr]
  ring

private theorem phaseCore_integral_cap
    (F : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ r : ℝ, R < r → F r = 0) :
    (∫ r : ℝ, F r ∂halfLineMeasure) = ∫ r in (0 : ℝ)..R, F r := by
  change (∫ r in Ioi (0 : ℝ), F r) = _
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (0 : ℝ) R ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  intro r hr
  have hrt : R < r := by
    by_contra h
    exact hr.2 ⟨hr.1, le_of_not_gt h⟩
  exact hzero r hrt

/-- Finite upper support gives full half-line energy membership. -/
theorem radialU_deriv_memLp_of_upperSupport
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ r : ℝ, R ≤ r → f r = 0) :
    MemLp (deriv (radialU f)) 2 halfLineMeasure := by
  have hc : Continuous (deriv (radialU f)) :=
    (radialU_contDiff_one f hf).continuous_deriv_one
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable.restrict).2
  have hfinite : IntegrableOn (fun r => (deriv (radialU f) r) ^ 2)
      (Ioc (0 : ℝ) R) :=
    ((hc.pow 2).intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := R)).1
  have htail : IntegrableOn (fun r => (deriv (radialU f) r) ^ 2) (Ioi R) := by
    apply (integrable_zero (μ := volume.restrict (Ioi R))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [phaseCore_U_deriv_zero f hf hcut hr]
    norm_num
  have hunion : Ioc (0 : ℝ) R ∪ Ioi R = Ioi (0 : ℝ) := by
    ext r
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hr, _⟩ | hr)
      · exact hr
      · exact lt_of_le_of_lt hR hr
    · intro hr
      by_cases hle : r ≤ R
      · exact Or.inl ⟨hr, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
  change IntegrableOn (fun r => (deriv (radialU f) r) ^ 2) (Ioi (0 : ℝ))
  rw [← hunion]
  exact hfinite.union htail

/-- Global reduced energy isometry, with the exterior derivative
vanishing derived from the support condition. -/
theorem radialU_global_energy_of_upperSupport
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ r : ℝ, R ≤ r → f r = 0) :
    (∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) =
      ∫ r : ℝ, r ^ 2 * (deriv f r) ^ 2 ∂halfLineMeasure := by
  calc
    (∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) =
        ∫ r in (0 : ℝ)..R, (deriv (radialU f) r) ^ 2 := by
      apply phaseCore_integral_cap _ R hR
      intro r hr
      rw [phaseCore_U_deriv_zero f hf hcut hr]
      norm_num
    _ = ∫ r in (0 : ℝ)..R, r ^ 2 * (deriv f r) ^ 2 :=
      radialU_energy_identity R f hf (hcut R le_rfl)
    _ = ∫ r : ℝ, r ^ 2 * (deriv f r) ^ 2 ∂halfLineMeasure := by
      symm
      apply phaseCore_integral_cap _ R hR
      intro r hr
      rw [phaseCore_deriv_zero f hcut hr]
      ring

/-- Actual 3D gradient energy equals the Hilbert coordinate norm, with
its geometric normalization and automatically proved membership. -/
theorem physicalRadial3_gradient_coordinate_of_upperSupport
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ r : ℝ, R ≤ r → f r = 0) :
    (∫ x : PhysicalRadialSpace3,
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) =
      (4 * Real.pi) * ‖smoothToRadialDotH1 f
        (radialU_deriv_memLp_of_upperSupport f hf R hR hcut)‖ ^ 2 := by
  rw [smoothRadialEnergy_coordinate_norm_sq,
    radialU_global_energy_of_upperSupport f hf R hR hcut]
  exact physicalRadial3_gradient_energy_integral f hf

/-- The phase form uses the actual 3D derivative and potential integrals. -/
def physicalRadial3PhaseQuadratic (f : ℝ → ℝ) : ℝ :=
  (∫ x : PhysicalRadialSpace3,
    ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) -
    3 * (∫ x : PhysicalRadialSpace3,
      bubble (‖x‖) ^ 4 * f (‖x‖) * f (‖x‖))

/-- Exact physical phase-Hessian form identification on the radial core.
No gradient identification, membership, or form equality is assumed. -/
theorem physicalRadial3_phase_core_eq_volterra
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ r : ℝ, R ≤ r → f r = 0) :
    physicalRadial3PhaseQuadratic f = (4 * Real.pi) *
      inner ℝ (weightedVolterraAMinus (smoothToRadialDotH1 f
        (radialU_deriv_memLp_of_upperSupport f hf R hR hcut)))
        (smoothToRadialDotH1 f
          (radialU_deriv_memLp_of_upperSupport f hf R hR hcut)) := by
  have hpair : (∫ r : ℝ, deriv (radialU f) r * deriv (radialU f) r
      ∂halfLineMeasure) =
      ∫ r : ℝ, r ^ 2 * (deriv f r) ^ 2 ∂halfLineMeasure := by
    simpa only [pow_two] using
      radialU_global_energy_of_upperSupport f hf R hR hcut
  rw [weightedVolterraAMinus_threeD_localPotential_bridge f f hf hf
    (radialU_deriv_memLp_of_upperSupport f hf R hR hcut)
    (radialU_deriv_memLp_of_upperSupport f hf R hR hcut), hpair]
  unfold physicalRadial3PhaseQuadratic
  rw [physicalRadial3_gradient_energy_integral f hf]

/-- Nonnegativity of the genuine physical phase form on the radial core. -/
theorem physicalRadial3_phase_core_nonnegative
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ r : ℝ, R ≤ r → f r = 0) :
    0 ≤ physicalRadial3PhaseQuadratic f := by
  rw [physicalRadial3_phase_core_eq_volterra f hf R hR hcut]
  exact mul_nonneg (by positivity) (weightedVolterraAMinus_nonneg _)

/-- A physical 4/5 energy bound, not merely a coefficient-space bound,
on core profiles satisfying the exact phase orthogonality condition. -/
theorem physicalRadial3_phase_core_coercive
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ r : ℝ, R ≤ r → f r = 0)
    (hphase : inner ℝ (weightedVolterraSineMode 0)
      (smoothToRadialDotH1 f
        (radialU_deriv_memLp_of_upperSupport f hf R hR hcut)) = 0) :
    (4 / 5 : ℝ) * (∫ x : PhysicalRadialSpace3,
        ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) ≤
      physicalRadial3PhaseQuadratic f := by
  rw [physicalRadial3_gradient_coordinate_of_upperSupport f hf R hR hcut,
    physicalRadial3_phase_core_eq_volterra f hf R hR hcut]
  have hgap := mul_le_mul_of_nonneg_left
    (weightedVolterraAMinus_tail_coercive _ hphase)
    (show (0 : ℝ) ≤ 4 * Real.pi by positivity)
  nlinarith only [hgap]

end HBL.Modulation.Monopole
