import HBL.MonopoleComplexResidual
import HBL.MonopoleProfileCancellation
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Prod

/-! Time integrability of actual compact core tests.  The nonlinear term is
the same absolutely convergent Hartree integral as in the static estimate.
Measurability is derived from the actual profiles and the parameter integral;
no measurability or integrability of a residual is supplied as a premise. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

private theorem monopoleRadialProfile_measurable : Measurable monopoleRadialProfile :=
  monopoleProfile_continuous.measurable.div measurable_id

/-- Joint measurability of the actual cutoff profile, including amplitude zero. -/
theorem monopoleMovingCutoffProfile_measurable :
    Measurable (fun p : ℝ × ℝ =>
      monopolePerturbedRadialProfile (monopoleQuadraticRadius p.1) p.1 p.2) := by
  simp_rw [monopoleMovingCutoffProfile_eq]
  have habs : Measurable (fun p : ℝ × ℝ => |p.1|) := by fun_prop
  exact (bubble_contDiff_infty.continuous.measurable.comp measurable_snd).add
    ((measurable_fst.mul (measurable_const.sub
      (cutoff_contDiff_infty.continuous.measurable.comp
        ((habs.mul measurable_snd).div_const 4)))).mul
          (monopoleRadialProfile_measurable.comp measurable_snd))

/-- The actual nonlinear Hartree expression is jointly measurable in the
amplitude and observation radius.  This uses its integral definition. -/
theorem monopoleMovingCutoffHartree_measurable :
    Measurable (fun p : ℝ × ℝ =>
      radialHartreeNonlinearity
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius p.1) p.1) p.2) := by
  have hrow : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      p.2 * hartreeRadialLog p.1.2 p.2 *
        monopolePerturbedRadialProfile (monopoleQuadraticRadius p.1.1) p.1.1 p.2 ^ 4) := by
    have hp : Measurable (fun p : (ℝ × ℝ) × ℝ =>
        monopolePerturbedRadialProfile (monopoleQuadraticRadius p.1.1) p.1.1 p.2) :=
      monopoleMovingCutoffProfile_measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hlog : Measurable (fun p : (ℝ × ℝ) × ℝ => hartreeRadialLog p.1.2 p.2) := by
      unfold hartreeRadialLog
      fun_prop
    exact (measurable_snd.mul hlog).mul (hp.pow_const 4)
  have hi := hrow.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))
  unfold radialHartreeNonlinearity radialHartreePotential
  exact ((measurable_const.div measurable_snd).mul hi.measurable).mul
    (monopoleMovingCutoffProfile_measurable.pow_const 3)

private theorem monopoleRadialProfile_deriv_differentiableAt {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (deriv monopoleRadialProfile) r :=
  (div_radius_second_hasDerivAt monopoleProfile
    (fun _ hx => (monopoleProfile_hasDerivAt hx).differentiableAt) hr
    (monopoleProfile_second_hasDerivAt hr).differentiableAt).differentiableAt

/-- A measurable representative of the dynamic effective core.  Its
nonlinearity uses the globally cutoff profile, not a bare constant tail. -/
def monopoleComplexCoreRepresentative (a v b omega r : ℝ) : ℂ :=
  ((radialLaplacian bubble r + a * radialLaplacian monopoleRadialProfile r +
    radialHartreeNonlinearity
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius a) a) r +
    a * monopolePerturbedRadialProfile (monopoleQuadraticRadius a) a r ^ 3 : ℝ) : ℂ) +
      monopoleComplexCoreFirstOrder a v b omega r

/-- Equality to the actual residual on its genuine cutoff core. -/
theorem monopoleComplexCoreRepresentative_eq {c : ℝ → ℝ} {cs s r : ℝ}
    (hc : HasDerivAt c cs s) (hr : 0 < r) (hcore : |c s| * r / 4 < 1)
    (b omega : ℝ) :
    monopoleComplexCoreRepresentative (c s) cs b omega r =
      monopoleComplexEffectiveIncrement c b omega s r := by
  have he : monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s) =ᶠ[𝓝 r]
      (fun x => bubble x + c s * monopoleRadialProfile x) := by
    have ht : Continuous (fun x : ℝ => |c s| * x / 4) := by fun_prop
    filter_upwards [ht.continuousAt.eventually (gt_mem_nhds hcore)] with x hx
    rw [monopoleMovingCutoffProfile_eq, cutoff_zero_of_le_one _ hx.le]
    ring
  have hLap : radialLaplacian
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s)) r =
      radialLaplacian bubble r + c s * radialLaplacian monopoleRadialProfile r := by
    calc
      _ = radialLaplacian (fun x => bubble x + c s * monopoleRadialProfile x) r := by
        unfold radialLaplacian
        rw [he.deriv_eq, he.deriv.deriv_eq]
      _ = _ := radialLaplacian_add_const_mul bubble monopoleRadialProfile (c s)
        (fun x _ => bubble_differentiable x)
        (fun _ hx => (monopoleRadialProfile_hasDerivAt hx).differentiableAt) hr
        ((contDiff_infty_iff_deriv.mp
          (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2).1 r)
        (monopoleRadialProfile_deriv_differentiableAt hr)
  rw [monopoleComplexEffectiveIncrement_core_eq hc hr hcore b omega,
    monopoleRadialStaticResidual, hLap]
  rfl

private theorem radialLaplacian_measurable (u : ℝ → ℝ) :
    Measurable (radialLaplacian u) := by
  exact (measurable_deriv (deriv u)).add
    ((measurable_const.div measurable_id).mul (measurable_deriv u))

private theorem monopoleDilation_measurable :
    Measurable (dilationGenerator monopoleRadialProfile) :=
  (monopoleRadialProfile_measurable.div_const 2).add
    (measurable_id.mul (measurable_deriv monopoleRadialProfile))

/-- Measurability of the actual core representative along measurable
parameter paths; the amplitude derivative is itself a measurable function. -/
theorem monopoleComplexCoreRepresentative_path_measurable
    {c b omega : ℝ → ℝ} (hc : Measurable c) (hb : Measurable b)
    (homega : Measurable omega) :
    Measurable (fun p : ℝ × ℝ =>
      monopoleComplexCoreRepresentative (c p.1) (deriv c p.1) (b p.1) (omega p.1) p.2) := by
  unfold monopoleComplexCoreRepresentative monopoleComplexCoreFirstOrder
  have hmap : Measurable (fun p : ℝ × ℝ => (c p.1, p.2)) :=
    (hc.comp measurable_fst).prodMk measurable_snd
  have hu : Measurable (fun p : ℝ × ℝ =>
      monopolePerturbedRadialProfile (monopoleQuadraticRadius (c p.1)) (c p.1) p.2) :=
    monopoleMovingCutoffProfile_measurable.comp hmap
  have hN := monopoleMovingCutoffHartree_measurable.comp hmap
  change Measurable (fun p : ℝ × ℝ =>
      radialHartreeNonlinearity
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius (c p.1)) (c p.1)) p.2) at hN
  have hLw : Measurable (fun p : ℝ × ℝ => radialLaplacian bubble p.2) :=
    (radialLaplacian_measurable bubble).comp measurable_snd
  have hLx : Measurable (fun p : ℝ × ℝ => radialLaplacian monopoleRadialProfile p.2) :=
    (radialLaplacian_measurable monopoleRadialProfile).comp measurable_snd
  have hx : Measurable (fun p : ℝ × ℝ => monopoleRadialProfile p.2) :=
    monopoleRadialProfile_measurable.comp measurable_snd
  have hd : Measurable (fun p : ℝ × ℝ => dilationGenerator monopoleRadialProfile p.2) :=
    monopoleDilation_measurable.comp measurable_snd
  have hcs : Measurable (fun p : ℝ × ℝ => deriv c p.1) :=
    (measurable_deriv c).comp measurable_fst
  have ha : Measurable (fun p : ℝ × ℝ => c p.1) := hc.comp measurable_fst
  have hbp : Measurable (fun p : ℝ × ℝ => b p.1) := hb.comp measurable_fst
  have how : Measurable (fun p : ℝ × ℝ => omega p.1) := homega.comp measurable_fst
  have hstatic : Measurable (fun p : ℝ × ℝ =>
      radialLaplacian bubble p.2 + c p.1 * radialLaplacian monopoleRadialProfile p.2 +
      radialHartreeNonlinearity
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius (c p.1)) (c p.1)) p.2 +
      c p.1 * monopolePerturbedRadialProfile (monopoleQuadraticRadius (c p.1)) (c p.1) p.2 ^ 3) :=
    ((hLw.add (ha.mul hLx)).add hN).add (ha.mul (hu.pow_const 3))
  apply Measurable.add
  · exact Complex.continuous_ofReal.measurable.comp hstatic
  · apply Measurable.add
    · apply Measurable.add
      · exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hcs.mul hx))
      · exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp ((hbp.mul ha).mul hd))
    · exact Complex.continuous_ofReal.measurable.comp ((how.mul ha).mul hx)

/-- The actual amplitude and velocity orders are integrable from the
primitive path decay bounds.  No residual bound is an input. -/
theorem monopoleParameterOrders_integrable
    {c b omega : ℝ → ℝ} {s0 beta A : ℝ}
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Measurable c) (hb : Measurable b) (homega : Measurable omega)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ)) :
    IntegrableOn (fun s => c s ^ 2) (Ioi s0) ∧
    IntegrableOn (fun s => |deriv c s|) (Ioi s0) ∧
    IntegrableOn (fun s => |b s * c s|) (Ioi s0) ∧
    IntegrableOn (fun s => |omega s * c s|) (Ioi s0) := by
  have hsq : IntegrableOn (fun s => c s ^ 2) (Ioi s0) := by
    apply integrableOn_of_abs_le_const_rpow s0 (-2 * beta) (A ^ 2) hs0
      (by linarith) _ (hc.pow_const 2).aestronglyMeasurable
    intro s hs
    have hp : 0 < s := hs0.trans hs
    have hc0 := (hdecay s hs).1
    have hp2 : s ^ (-2 * beta) = s ^ (-beta) * s ^ (-beta) := by
      rw [show -2 * beta = -beta + -beta by ring, Real.rpow_add hp]
    calc
      |c s ^ 2| = |c s| * |c s| := by rw [abs_pow, pow_two]
      _ ≤ (A * s ^ (-beta)) * (A * s ^ (-beta)) :=
        mul_le_mul hc0 hc0 (abs_nonneg _) (by positivity)
      _ = A ^ 2 * s ^ (-2 * beta) := by rw [hp2]; ring
  have hvel : IntegrableOn (fun s => |deriv c s|) (Ioi s0) := by
    apply integrableOn_of_abs_le_const_rpow s0 (-1 - beta) A hs0
      (by linarith) _
      (by simpa only [Real.norm_eq_abs] using (measurable_deriv c).norm.aestronglyMeasurable)
    intro s hs
    simpa only [abs_abs] using (hdecay s hs).2.1
  have hprod (d : ℝ → ℝ) (hd : Measurable d)
      (hdb : ∀ s : ℝ, s0 < s → |d s| ≤ A * s ^ (-1 : ℝ)) :
      IntegrableOn (fun s => |d s * c s|) (Ioi s0) := by
    apply integrableOn_of_abs_le_const_rpow s0 (-1 - beta) (A ^ 2) hs0
      (by linarith) _
      (by simpa only [Real.norm_eq_abs, Pi.mul_apply] using (hd.mul hc).norm.aestronglyMeasurable)
    intro s hs
    have hp : 0 < s := hs0.trans hs
    have hp2 : s ^ (-1 - beta) = s ^ (-1 : ℝ) * s ^ (-beta) := by
      rw [sub_eq_add_neg, Real.rpow_add hp]
    calc
      |(|d s * c s|)| = |d s| * |c s| := by rw [abs_abs, abs_mul]
      _ ≤ (A * s ^ (-1 : ℝ)) * (A * s ^ (-beta)) :=
        mul_le_mul (hdb s hs) (hdecay s hs).1 (abs_nonneg _) (by positivity)
      _ = A ^ 2 * s ^ (-1 - beta) := by rw [hp2]; ring
  exact ⟨hsq, hvel, hprod b hb (fun s hs => (hdecay s hs).2.2.1),
    hprod omega homega (fun s hs => (hdecay s hs).2.2.2)⟩

/-- The actual complex compact threshold test, retaining the radial
conjugation factor r.  The fixed normalized tests vanish outside this core. -/
def monopoleComplexCoreProjection (zeta c b omega : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ r in Ioo (0 : ℝ) 1,
    (r * zeta r : ℝ) * monopoleComplexEffectiveIncrement c (b s) (omega s) s r

/-- Actual compact core integrals exist at every admissible time, and the
resulting scalar projection is integrable in time.  All hypotheses concern
the primitive parameter paths and the fixed test function. -/
theorem monopoleComplexCoreProjection_integrable
    {zeta c b omega : ℝ → ℝ} {s0 beta A : ℝ}
    (hzeta : Continuous zeta) (hs0 : 0 < s0)
    (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ)) :
    (∀ s : ℝ, s0 < s → IntegrableOn
      (fun r => (r * zeta r : ℝ) *
        monopoleComplexEffectiveIncrement c (b s) (omega s) s r) (Ioo (0 : ℝ) 1)) ∧
    IntegrableOn (monopoleComplexCoreProjection zeta c b omega) (Ioi s0) := by
  obtain ⟨D, hD, hDbound⟩ := monopoleComplexEffectiveIncrement_core_bound
  let E : ℝ → ℝ := fun s =>
    monopoleStaticRadialBoundConstant * (c s) ^ 2 +
    monopoleRadialBoundConstant * |deriv c s| + D * |b s * c s| +
    monopoleRadialBoundConstant * |omega s * c s|
  have horders := monopoleParameterOrders_integrable hs0 hbeta hA
    hc.continuous.measurable hb homega hdecay
  have hEi : IntegrableOn E (Ioi s0) :=
    (((horders.1.const_mul monopoleStaticRadialBoundConstant).add
      (horders.2.1.const_mul monopoleRadialBoundConstant)).add
      (horders.2.2.1.const_mul D)).add
      (horders.2.2.2.const_mul monopoleRadialBoundConstant)
  obtain ⟨Z, hZ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) (continuous_id.mul hzeta).continuousOn
  let F : ℝ × ℝ → ℂ := fun p =>
    (p.2 * zeta p.2 : ℝ) *
      monopoleComplexCoreRepresentative (c p.1) (deriv c p.1) (b p.1) (omega p.1) p.2
  have hw : Measurable (fun p : ℝ × ℝ => ((p.2 * zeta p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_snd.mul (hzeta.measurable.comp measurable_snd))
  have hFm : Measurable F := hw.mul
    (monopoleComplexCoreRepresentative_path_measurable hc.continuous.measurable hb homega)
  have hcore (s : ℝ) (hs : s0 < s) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      |c s| * r / 4 ≤ 1 / 2 := by
    have hcr : |c s| * r ≤ 1 :=
      (mul_le_mul (hsmall s hs) hr.2.le hr.1.le zero_le_one).trans_eq (one_mul 1)
    linarith
  have heq (s : ℝ) (hs : s0 < s) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      F (s, r) = (r * zeta r : ℝ) *
        monopoleComplexEffectiveIncrement c (b s) (omega s) s r := by
    dsimp only [F]
    rw [monopoleComplexCoreRepresentative_eq (hc s).hasDerivAt hr.1
      (by have := hcore s hs r hr; linarith) (b s) (omega s)]
  have hbound (s : ℝ) (hs : s0 < s) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      ‖F (s, r)‖ ≤ |Z| * E s := by
    rw [heq s hs r hr, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hz : |r * zeta r| ≤ |Z| := by
      exact (hZ r ⟨hr.1.le, hr.2.le⟩).trans (le_abs_self Z)
    exact mul_le_mul hz
      (hDbound c (deriv c s) s r (b s) (omega s) (hc s).hasDerivAt
        (hsmall s hs) hr.1 (hcore s hs r hr))
      (norm_nonneg _) (abs_nonneg Z)
  have hrow (s : ℝ) (hs : s0 < s) :
      IntegrableOn (fun r => F (s, r)) (Ioo (0 : ℝ) 1) := by
    refine (integrable_const (|Z| * E s)).mono'
      (hFm.comp measurable_prodMk_left).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hbound s hs r hr
  have hrows : ∀ s : ℝ, s0 < s → IntegrableOn
      (fun r => (r * zeta r : ℝ) *
        monopoleComplexEffectiveIncrement c (b s) (omega s) s r) (Ioo (0 : ℝ) 1) := by
    intro s hs
    apply (hrow s hs).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact heq s hs r hr
  have hprojEq (s : ℝ) (hs : s0 < s) :
      (∫ r in Ioo (0 : ℝ) 1, F (s, r)) =
        monopoleComplexCoreProjection zeta c b omega s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact heq s hs r hr
  have hprojInt : IntegrableOn (fun s => ∫ r in Ioo (0 : ℝ) 1, F (s, r)) (Ioi s0) := by
    apply ((hEi.const_mul |Z|).mul_const
      ((volume.restrict (Ioo (0 : ℝ) 1)).real univ)).mono'
      hFm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact norm_integral_le_of_norm_le_const (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hbound s hs r hr)
  refine ⟨hrows, hprojInt.congr ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact hprojEq s hs

end HBL.Modulation.Monopole
