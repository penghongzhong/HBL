import HBL.MonopoleCoreIntegrability
import HBL.ThresholdTestExistence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The fixed manuscript coordinate tests applied to the actual effective
radial cutoff residual.  Full positive-half-line integrals and the original
compactThresholdPairing are identified explicitly.  Noncompact resonance
charges and transported slow-frame tests are not asserted here. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

private theorem supported_halfLine_integral_eq_core {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (hf : ∀ r : ℝ, 1 ≤ r → f r = 0) :
    (∫ r in Ioi (0 : ℝ), f r) = ∫ r in Ioo (0 : ℝ) 1, f r := by
  have h := integral_union_eq_left_of_forall (μ := volume) (s := Ioo (0 : ℝ) 1)
    (t := Ici (1 : ℝ)) (f := f) measurableSet_Ici hf
  rwa [Ioo_union_Ici_eq_Ioi (by norm_num : (0 : ℝ) < 1)] at h

private theorem supported_halfLine_integrable {E : Type*}
    [NormedAddCommGroup E] (f : ℝ → E)
    (hf : ∀ r : ℝ, 1 ≤ r → f r = 0)
    (hcore : IntegrableOn f (Ioo (0 : ℝ) 1)) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  have htail : IntegrableOn f (Ici (1 : ℝ)) := by
    apply integrableOn_zero.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    exact (hf r hr).symm
  simpa only [Ioo_union_Ici_eq_Ioi (by norm_num : (0 : ℝ) < 1)] using
    hcore.union htail

/-- The complete positive-half-line coordinate integral of the actual
complex radial effective residual, with the factor from U f = r f. -/
def monopoleComplexFullProjection (zeta c b omega : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ),
    (r * zeta r : ℝ) * monopoleComplexEffectiveIncrement c (b s) (omega s) s r

/-- Compact support gives an exact identity of the actual full and core
integrals. Absolute convergence is established separately below. -/
theorem monopoleComplexFullProjection_eq_core
    (zeta c b omega : ℝ → ℝ)
    (hsupp : ∀ r : ℝ, 1 ≤ r → zeta r = 0) (s : ℝ) :
    monopoleComplexFullProjection zeta c b omega s =
      monopoleComplexCoreProjection zeta c b omega s := by
  apply supported_halfLine_integral_eq_core
  intro r hr
  simp only [hsupp r hr, mul_zero, Complex.ofReal_zero, zero_mul]

/-- Full spatial row convergence and time integrability for the same
actual compactly supported coordinate integral, derived from primitive paths. -/
theorem monopoleComplexFullProjection_integrable
    {zeta c b omega : ℝ → ℝ} {s0 beta A : ℝ}
    (hzeta : Continuous zeta) (hsupp : ∀ r : ℝ, 1 ≤ r → zeta r = 0)
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ)) :
    (∀ s : ℝ, s0 < s → IntegrableOn
      (fun r => (r * zeta r : ℝ) *
        monopoleComplexEffectiveIncrement c (b s) (omega s) s r) (Ioi (0 : ℝ))) ∧
    IntegrableOn (monopoleComplexFullProjection zeta c b omega) (Ioi s0) := by
  have hcore := monopoleComplexCoreProjection_integrable hzeta hs0 hbeta hA
    hc hb homega hsmall hdecay
  refine ⟨?_, ?_⟩
  · intro s hs
    apply supported_halfLine_integrable _ _ (hcore.1 s hs)
    intro r hr
    simp only [hsupp r hr, mul_zero, Complex.ofReal_zero, zero_mul]
  · have he : monopoleComplexFullProjection zeta c b omega =
        monopoleComplexCoreProjection zeta c b omega :=
      funext (monopoleComplexFullProjection_eq_core zeta c b omega hsupp)
    rw [he]
    exact hcore.2

/-- The real coordinate from the already certified first manuscript lemma,
applied to the actual effective residual by its original compact integral. -/
def monopoleThresholdCoordinatePlus (c b omega : ℝ → ℝ) (s : ℝ) : ℝ :=
  compactThresholdPairing (Real.exp 1) normalizedZetaPlus
    (fun r => (monopoleComplexEffectiveIncrement c (b s) (omega s) s r).re)

/-- The imaginary coordinate uses the same fixed normalized phase test. -/
def monopoleThresholdCoordinateMinus (c b omega : ℝ → ℝ) (s : ℝ) : ℝ :=
  compactThresholdPairing (Real.exp 1) normalizedZetaMinus
    (fun r => (monopoleComplexEffectiveIncrement c (b s) (omega s) s r).im)

private theorem compactThresholdPairing_eq_halfLine (zeta f : ℝ → ℝ)
    (hsupp : ∀ r : ℝ, 1 ≤ r → zeta r = 0) :
    compactThresholdPairing (Real.exp 1) zeta f =
      ∫ r in Ioi (0 : ℝ), zeta r * radialU f r := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have ht : ∀ r ∈ Ici (Real.exp (1 : ℝ)), zeta r * radialU f r = 0 := by
    intro r hr
    rw [hsupp r (he.trans hr), zero_mul]
  have h := integral_union_eq_left_of_forall (μ := volume)
    (s := Ioo (0 : ℝ) (Real.exp 1))
    (t := Ici (Real.exp 1)) measurableSet_Ici ht
  rw [Ioo_union_Ici_eq_Ioi (Real.exp_pos 1)] at h
  unfold compactThresholdPairing
  rw [integral_Ioc_eq_integral_Ioo]
  exact h.symm

/-- Exact equality to the manuscript real threshold pairing on the full
positive half-line; no anonymous functional replaces the fixed test. -/
theorem monopoleThresholdCoordinatePlus_eq_halfLine (c b omega : ℝ → ℝ) (s : ℝ) :
    monopoleThresholdCoordinatePlus c b omega s =
      ∫ r in Ioi (0 : ℝ), normalizedZetaPlus r * radialU
        (fun x => (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).re) r :=
  compactThresholdPairing_eq_halfLine _ _ normalizedZetaPlus_zero_of_one_le

/-- Exact equality to the manuscript imaginary threshold pairing on the
full positive half-line. -/
theorem monopoleThresholdCoordinateMinus_eq_halfLine (c b omega : ℝ → ℝ) (s : ℝ) :
    monopoleThresholdCoordinateMinus c b omega s =
      ∫ r in Ioi (0 : ℝ), normalizedZetaMinus r * radialU
        (fun x => (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).im) r :=
  compactThresholdPairing_eq_halfLine _ _ normalizedZetaMinus_zero_of_one_le

private theorem monopoleThresholdCoordinatePlus_eq_full_re
    (c b omega : ℝ → ℝ) (s : ℝ)
    (hrow : IntegrableOn (fun r => (r * normalizedZetaPlus r : ℝ) *
      monopoleComplexEffectiveIncrement c (b s) (omega s) s r) (Ioi (0 : ℝ))) :
    monopoleThresholdCoordinatePlus c b omega s =
      (monopoleComplexFullProjection normalizedZetaPlus c b omega s).re := by
  rw [monopoleThresholdCoordinatePlus_eq_halfLine]
  simpa [monopoleComplexFullProjection, radialU, mul_comm, mul_left_comm, mul_assoc] using
    integral_re hrow

private theorem monopoleThresholdCoordinateMinus_eq_full_im
    (c b omega : ℝ → ℝ) (s : ℝ)
    (hrow : IntegrableOn (fun r => (r * normalizedZetaMinus r : ℝ) *
      monopoleComplexEffectiveIncrement c (b s) (omega s) s r) (Ioi (0 : ℝ))) :
    monopoleThresholdCoordinateMinus c b omega s =
      (monopoleComplexFullProjection normalizedZetaMinus c b omega s).im := by
  rw [monopoleThresholdCoordinateMinus_eq_halfLine]
  simpa [monopoleComplexFullProjection, radialU, mul_comm, mul_left_comm, mul_assoc] using
    integral_im hrow

/-- The two actual normalized manuscript coordinates have absolutely
convergent full spatial pairings and are integrable in time. -/
theorem monopoleThresholdCoordinates_integrable
    {c b omega : ℝ → ℝ} {s0 beta A : ℝ}
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ)) :
    (∀ s : ℝ, s0 < s →
      IntegrableOn (fun r => normalizedZetaPlus r * radialU
        (fun x => (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).re) r)
        (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun r => normalizedZetaMinus r * radialU
        (fun x => (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).im) r)
        (Ioi (0 : ℝ))) ∧
    IntegrableOn (monopoleThresholdCoordinatePlus c b omega) (Ioi s0) ∧
    IntegrableOn (monopoleThresholdCoordinateMinus c b omega) (Ioi s0) := by
  have hp := monopoleComplexFullProjection_integrable
    normalizedZetaPlus_contDiff_infty.continuous normalizedZetaPlus_zero_of_one_le
    hs0 hbeta hA hc hb homega hsmall hdecay
  have hm := monopoleComplexFullProjection_integrable
    normalizedZetaMinus_contDiff_infty.continuous normalizedZetaMinus_zero_of_one_le
    hs0 hbeta hA hc hb homega hsmall hdecay
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    constructor
    · simpa [radialU, mul_comm, mul_left_comm, mul_assoc] using (hp.1 s hs).re
    · simpa [radialU, mul_comm, mul_left_comm, mul_assoc] using (hm.1 s hs).im
  · apply hp.2.re.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (monopoleThresholdCoordinatePlus_eq_full_re c b omega s (hp.1 s hs)).symm
  · apply hm.2.im.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (monopoleThresholdCoordinateMinus_eq_full_im c b omega s (hm.1 s hs)).symm

/-- Complete certification of revised manuscript environment 2.6: actual
Hartree row convergence, static quadratic core cancellation, the exact
complex dynamic formula, and the original fixed coordinate projections in
space and time. Only primitive amplitude/scaling/phase regularity and decay
are inputs. The original stronger three-dimensional matching claim remains
a separate obligation of the finite-profile construction. -/
theorem revisedMonopoleCoreManuscriptEnvironment_closed
    {c b omega : ℝ → ℝ} {s0 beta A : ℝ}
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ)) :
    (∀ s : ℝ, s0 < s → ∀ r : ℝ, 0 < r → r ≤ 1 →
      IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
        monopolePerturbedRadialProfile (monopoleQuadraticRadius (c s)) (c s) rho ^ 4)
        (Ioi (0 : ℝ)) ∧
      |monopoleRadialStaticResidual (monopoleQuadraticRadius (c s)) (c s) r| ≤
        monopoleStaticRadialBoundConstant * (c s) ^ 2 ∧
      monopoleComplexEffectiveIncrement c (b s) (omega s) s r =
        (monopoleRadialStaticResidual (monopoleQuadraticRadius (c s)) (c s) r : ℂ) +
          monopoleComplexCoreFirstOrder (c s) (deriv c s) (b s) (omega s) r) ∧
    (∀ s : ℝ, s0 < s →
      IntegrableOn (fun r => normalizedZetaPlus r * radialU
        (fun x => (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).re) r)
        (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun r => normalizedZetaMinus r * radialU
        (fun x => (monopoleComplexEffectiveIncrement c (b s) (omega s) s x).im) r)
        (Ioi (0 : ℝ))) ∧
    IntegrableOn (monopoleThresholdCoordinatePlus c b omega) (Ioi s0) ∧
    IntegrableOn (monopoleThresholdCoordinateMinus c b omega) (Ioi s0) := by
  have hcoords := monopoleThresholdCoordinates_integrable
    hs0 hbeta hA hc hb homega hsmall hdecay
  refine ⟨?_, hcoords⟩
  intro s hs r hr hr1
  have hcore : |c s| * r / 4 ≤ 1 / 2 := by
    have hcr : |c s| * r ≤ 1 :=
      (mul_le_mul (hsmall s hs) hr1 hr.le zero_le_one).trans_eq (one_mul 1)
    linarith
  have hstatic := monopoleRadialStaticResidual_core_quadratic_control_all
    (hsmall s hs) hr hcore
  exact ⟨hstatic.1, hstatic.2,
    monopoleComplexEffectiveIncrement_core_eq (hc s).hasDerivAt hr
      (by linarith) (b s) (omega s)⟩

end HBL.Modulation.Monopole
