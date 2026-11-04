import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedInnerResponse
import HBL.InnerEstimates.PlusOutputClassical
import HBL.InnerEstimates.MinusOutputClassical
import HBL.MonopoleRadialLinearization
import Mathlib.Tactic

/-!
The same normalized scale/phase responses used by the accepted coupled
matrix solve the genuine positive-radius classical radial equations.
The factors r*Q and r*V extend continuously through zero: the quotient
in the monopole disappears after radial conjugation.  Consequently the
existing normalized Fredholm classical theorem applies without a new
source-continuity assumption or a new choice of inner solution.

The quotient Laplacian and the real-channel Riesz term are transported
back to physical radial variables, with actual row integrability.  These
are the fixed bubble Hessian equations; the difference from the moving
background Hessian, time terms, and nonlinear residual gain remain to be
controlled in the physical correction step.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

private theorem actual_monopole_profile_C1 :
    Differentiable ℝ monopoleProfile ∧ Continuous (deriv monopoleProfile) := by
  have hg := halfLineMinGreen_C1_of_integrable
    monopoleRemainderSource monopoleRemainderSource_integrable
  have he : monopoleRemainder = halfLineMinGreen monopoleRemainderSource :=
    funext monopoleRemainder_eq_halfLineMinGreen
  have hl := (contDiff_infty_iff_deriv.mp monopoleLogModel_contDiff_infty).1
  have hm := (contDiff_infty_iff_deriv.mp model_contDiff_infty).1
  let D : ℝ → ℝ := fun r =>
    deriv monopoleLogModel r + monopoleAffineSlope * deriv model r +
      halfLineL1GreenSlope monopoleRemainderSource r
  have hd (r : ℝ) : HasDerivAt monopoleProfile (D r) r := by
    have hrem : HasDerivAt monopoleRemainder
        (halfLineL1GreenSlope monopoleRemainderSource r) r := by
      rw [he]
      exact hg.1 r
    exact ((hl r).hasDerivAt.add
      ((hm r).hasDerivAt.const_mul monopoleAffineSlope)).add hrem
  refine ⟨fun r => (hd r).differentiableAt, ?_⟩
  have hder : deriv monopoleProfile = D := funext fun r => (hd r).deriv
  rw [hder]
  exact (((contDiff_infty_iff_deriv.mp monopoleLogModel_contDiff_infty).2.continuous).add
    (((contDiff_infty_iff_deriv.mp model_contDiff_infty).2.continuous).const_mul
      monopoleAffineSlope)).add hg.2

private theorem actual_phase_conjugated_source_eq (R c r : ℝ) :
    actualMomentLockedInnerPhaseSource R c r =
      actualHartreeInnerSourceCutoff R r *
        (r * bubble r + c * (1 - cutoff (|c| * r / 4)) * monopoleProfile r) := by
  by_cases hr : r = 0
  · subst r
    simp [actualMomentLockedInnerPhaseSource, monopoleProfile_zero]
  · unfold actualMomentLockedInnerPhaseSource actualMomentLockedCore
    rw [monopoleMovingCutoffProfile_eq]
    unfold monopoleRadialProfile
    field_simp [hr] <;> ring

private theorem actual_scale_conjugated_source_eq (R c r : ℝ) :
    actualMomentLockedInnerScaleSource R c r =
      actualHartreeInnerSourceCutoff R r *
        (r * dilationGenerator bubble r +
          c * (1 - cutoff (|c| * r / 4)) *
            (r * deriv monopoleProfile r - (3 / 2 : ℝ) * monopoleProfile r)) := by
  by_cases hr : r = 0
  · subst r
    simp [actualMomentLockedInnerScaleSource, monopoleProfile_zero]
  · have hp := actual_monopole_profile_C1.1 r
    have hq : HasDerivAt (fun x : ℝ => monopoleProfile x / x)
        ((deriv monopoleProfile r * r - monopoleProfile r) / r ^ 2) r := by
      simpa only [mul_one] using hp.hasDerivAt.div (hasDerivAt_id r) hr
    have harg : HasDerivAt (fun x : ℝ => |c| * x / 4) (|c| / 4) r := by
      convert ((hasDerivAt_id r).const_mul |c|).div_const 4 using 1 <;> simp
    have hcut := ((contDiff_infty_iff_deriv.mp cutoff_contDiff_infty).1
      (|c| * r / 4)).hasDerivAt.comp r harg
    have hcore : actualMomentLockedCore c =
        (fun x : ℝ => bubble x +
          c * (1 - cutoff (|c| * x / 4)) * (monopoleProfile x / x)) := by
      funext x
      exact monopoleMovingCutoffProfile_eq c x
    have hd : deriv (actualMomentLockedCore c) r =
        deriv bubble r +
          (c * (0 - deriv cutoff (|c| * r / 4) * (|c| / 4)) *
              (monopoleProfile r / r) +
            c * (1 - cutoff (|c| * r / 4)) *
              ((deriv monopoleProfile r * r - monopoleProfile r) / r ^ 2)) := by
      rw [hcore]
      exact ((bubble_differentiable r).hasDerivAt.add
        ((((hasDerivAt_const r (1 : ℝ)).sub hcut).const_mul c).mul hq)).deriv
    unfold actualMomentLockedInnerScaleSource actualMomentLockedScaleProfile
      actualMomentLockedAmplitudeTangent dilationGenerator
    rw [hd, congrFun hcore r]
    unfold monopoleRadialProfile
    field_simp [hr] <;> ring

/-- Both actual radially conjugated speed sources are globally continuous.
The origin is proved using the vanished monopole numerator, not supplied
as a regularity hypothesis on a totalized quotient. -/
theorem actual_Hartree_moment_locked_inner_sources_continuous (R c : ℝ) :
    Continuous (actualMomentLockedInnerScaleSource R c) ∧
      Continuous (actualMomentLockedInnerPhaseSource R c) := by
  have hp : Continuous monopoleProfile := monopoleProfile_continuous
  have hdp : Continuous (deriv monopoleProfile) := actual_monopole_profile_C1.2
  have hw : Continuous bubble := bubble_contDiff_infty.continuous
  have hdw : Continuous (deriv bubble) :=
    (contDiff_infty_iff_deriv.mp bubble_contDiff_infty).2.continuous
  have hcut : Continuous cutoff := cutoff_contDiff_infty.continuous
  have heta := actual_Hartree_inner_source_cutoff_continuous R
  constructor
  · have he : actualMomentLockedInnerScaleSource R c =
        (fun r => actualHartreeInnerSourceCutoff R r *
          (r * dilationGenerator bubble r +
            c * (1 - cutoff (|c| * r / 4)) *
              (r * deriv monopoleProfile r - (3 / 2 : ℝ) * monopoleProfile r))) :=
      funext fun r => actual_scale_conjugated_source_eq R c r
    rw [he]
    unfold dilationGenerator
    fun_prop
  · have he : actualMomentLockedInnerPhaseSource R c =
        (fun r => actualHartreeInnerSourceCutoff R r *
          (r * bubble r + c * (1 - cutoff (|c| * r / 4)) * monopoleProfile r)) :=
      funext fun r => actual_phase_conjugated_source_eq R c r
    rw [he]
    fun_prop

/-- The already chosen responses satisfy the original classical H-minus
and H-plus equations, with the original sources and forced charges. -/
theorem actual_Hartree_moment_locked_inner_responses_classical
    (R c : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (actualMomentLockedInnerScaleResponse R c hR) r ∧
      DifferentiableAt ℝ (deriv (actualMomentLockedInnerScaleResponse R c hR)) r ∧
      DifferentiableAt ℝ (actualMomentLockedInnerPhaseResponse R c hR) r ∧
      DifferentiableAt ℝ (deriv (actualMomentLockedInnerPhaseResponse R c hR)) r ∧
      hMinusApply (actualMomentLockedInnerScaleResponse R c hR) r =
        actualMomentLockedInnerScaleSource R c r ∧
      hPlusApply (actualMomentLockedInnerPhaseResponse R c hR) r =
        actualMomentLockedInnerPhaseSource R c r := by
  have hcont := actual_Hartree_moment_locked_inner_sources_continuous R c
  have hweight := actual_Hartree_moment_locked_inner_sources_weighted R c hR
  have hb := normalizedMinusOutput_classical
    (7 / 4 : ℝ) (by norm_num) (by norm_num) _ hweight.1 hcont.1 r hr
  have hw := normalizedPlusOutput_classical
    (7 / 4 : ℝ) (by norm_num) (by norm_num) _ hweight.2 hcont.2 r hr
  exact ⟨hb.1, hb.2.1, hw.1, hw.2.1, hb.2.2, hw.2.2⟩

private theorem actual_nonlocal_quotient_bridge
    (q : ℝ → ℝ)
    (hq : MemLp (fun rho => weightedGreenDecay rho * q rho) 2 halfLineMeasure)
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
      (bubble rho ^ 3 * (q rho / rho))) (Ioi (0 : ℝ)) ∧
      nonlocalApply q r = 4 * r * bubble r ^ 3 *
        radialHartreePotential (fun rho => bubble rho ^ 3 * (q rho / rho)) r := by
  let C : ℝ := 8 * Real.pi * hartreeKappa * bubble r ^ 3
  let f : ℝ → ℝ := fun rho => rho * hartreeRadialLog r rho *
    (bubble rho ^ 3 * (q rho / rho))
  have hC : C ≠ 0 := by
    dsimp [C, hartreeKappa, bubble]
    positivity
  have he : (fun rho => hartreeKernel r rho * q rho) =ᵐ[halfLineMeasure]
      (fun rho => C * f rho) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
    change 0 < rho at hrho
    dsimp [C, f, hartreeKernel, hartreeRadialLog]
    field_simp [hrho.ne'] <;> ring
  have hint := nonlocalApply_integrable_of_weighted_memLp q hq hr.le
  have hf : Integrable f halfLineMeasure := by
    apply (hint.const_mul C⁻¹).congr
    filter_upwards [he] with rho heq
    rw [heq]
    exact inv_mul_cancel_left₀ hC (f rho)
  refine ⟨hf, ?_⟩
  unfold nonlocalApply
  change (∫ rho, hartreeKernel r rho * q rho ∂halfLineMeasure) = _
  rw [integral_congr_ae he, integral_const_mul]
  dsimp [C, f, radialHartreePotential]
  change (8 * Real.pi * hartreeKappa * bubble r ^ 3) *
      (∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho *
        (bubble rho ^ 3 * (q rho / rho))) = _
  field_simp [hr.ne'] <;> ring

/-- Physical positive-radius equations of the SAME actual inner responses.
Both quotient derivatives are justified, the full real-channel Riesz row
is absolutely integrable, and the signs are those of additive correction
against the fixed bubble Hessian. -/
theorem actual_Hartree_moment_locked_inner_physical_equations
    (R c : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 < r) :
    let qb := actualMomentLockedInnerScaleResponse R c hR
    let qw := actualMomentLockedInnerPhaseResponse R c hR
    DifferentiableAt ℝ (fun x => qb x / x) r ∧
      DifferentiableAt ℝ (deriv (fun x => qb x / x)) r ∧
      DifferentiableAt ℝ (fun x => qw x / x) r ∧
      DifferentiableAt ℝ (deriv (fun x => qw x / x)) r ∧
      IntegrableOn (fun rho => rho * hartreeRadialLog r rho *
        (bubble rho ^ 3 * (qw rho / rho))) (Ioi (0 : ℝ)) ∧
      radialLaplacian (fun x => qb x / x) r +
          3 * bubble r ^ 4 * (qb r / r) =
        -(actualHartreeInnerSourceCutoff R r * actualMomentLockedScaleProfile c r) ∧
      radialLaplacian (fun x => qw x / x) r +
          9 * bubble r ^ 4 * (qw r / r) +
          4 * bubble r ^ 3 * radialHartreePotential
            (fun rho => bubble rho ^ 3 * (qw rho / rho)) r =
        -(actualHartreeInnerSourceCutoff R r * actualMomentLockedCore c r) := by
  let qb := actualMomentLockedInnerScaleResponse R c hR
  let qw := actualMomentLockedInnerPhaseResponse R c hR
  have hclass := actual_Hartree_moment_locked_inner_responses_classical R c hR
  have hb : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ qb x :=
    fun x hx => (hclass x hx).1
  have hw : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ qw x :=
    fun x hx => (hclass x hx).2.2.1
  have hb2 : DifferentiableAt ℝ (deriv qb) r := (hclass r hr).2.1
  have hw2 : DifferentiableAt ℝ (deriv qw) r := (hclass r hr).2.2.2.1
  have hprops := actual_Hartree_moment_locked_inner_responses_C1 R c hR
  have hwmem : MemLp (fun x => weightedGreenDecay x * qw x) 2 halfLineMeasure := by
    have h : InWeightedL2 (-(2 : ℝ)) qw :=
      hprops.2.1.2.2.1 2 (by norm_num)
    simpa [InWeightedL2, affineJapaneseWeight, weightedGreenDecay, Real.rpow_neg_one] using h
  have hnonlocal := actual_nonlocal_quotient_bridge qw hwmem r hr
  have hv : potential r = 3 * bubble r ^ 4 := by
    unfold potential
    rw [show bubble r ^ 4 = (bubble r ^ 2) ^ 2 by ring, bubble_sq, inv_pow]
    ring
  dsimp only
  refine ⟨(div_radius_hasDerivAt qb hr (hb r hr)).differentiableAt,
    (div_radius_second_hasDerivAt qb hb hr hb2).differentiableAt,
    (div_radius_hasDerivAt qw hr (hw r hr)).differentiableAt,
    (div_radius_second_hasDerivAt qw hw hr hw2).differentiableAt,
    hnonlocal.1, ?_, ?_⟩
  · have hconj : radialLaplacian (fun x => qb x / x) r +
        3 * bubble r ^ 4 * (qb r / r) = -hMinusApply qb r / r := by
      rw [radialLaplacian_div_radius qb hb hr hb2]
      unfold hMinusApply
      rw [hv]
      ring
    rw [hconj, (hclass r hr).2.2.2.2.1]
    unfold actualMomentLockedInnerScaleSource
    field_simp [hr.ne'] <;> ring
  · have hconj : radialLaplacian (fun x => qw x / x) r +
        9 * bubble r ^ 4 * (qw r / r) +
        4 * bubble r ^ 3 * radialHartreePotential
          (fun rho => bubble rho ^ 3 * (qw rho / rho)) r =
        -hPlusApply qw r / r := by
      rw [radialLaplacian_div_radius qw hw hr hw2]
      unfold hPlusApply
      rw [hv, hnonlocal.2]
      field_simp [hr.ne'] <;> ring
    rw [hconj, (hclass r hr).2.2.2.2.2]
    unfold actualMomentLockedInnerPhaseSource
    field_simp [hr.ne'] <;> ring

end HBL.TypeIIDynamicSelection
