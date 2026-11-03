import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import HBL.InnerReconstruction.ActualTwoChannelReconstruction
import HBL.InnerReconstruction.AffineRestorationProperties
import HBL.InnerReconstruction.GreenC1Integrable
import Mathlib.Tactic

/-!
The actual source is G=r*(1-chi(r/R))*F, R=ell^(-1/16).
Its two normalized Fredholm solutions are reconstructed by the existing
Green representatives, then their forced affine tails are restored.
L1 source integration, rather than an extra continuity hypothesis on F,
gives C1 representatives.  Physical Kummer traces belong to u=q/r:
u'(r)=(r*q'(r)-q(r))/r^2, not q'(r).

The exported statement retains EXACT Green reconstruction identities,
not only existential smooth functions with the desired affine slopes.
Together with the weighted a.e. identities these are the original
normalized Fredholm fixed-point equations in representative form.
This theorem does not claim small trace norms, simultaneous two-interface
matching, C2 regularity for measurable forcing, or Type-II blowup.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

private theorem representative_c1_from_weighted
    (g : RealL2 halfLineMeasure) (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (F : ℝ → ℝ) (hF : InWeightedL2 sigma F) :
    Differentiable ℝ (innerGreenRepresentative g F) ∧
      Continuous (deriv (innerGreenRepresentative g F)) := by
  have hG := halfLineMinGreen_C1_of_integrable
    (fun r : ℝ => weightedGreenDecay r * g r)
    (weightedGreen_source_integrable g)
  have hS := halfLineMinGreen_C1_of_integrable F
    (weightedSource_integrable sigma hsigma F hF)
  let slope : ℝ → ℝ := fun r =>
    halfLineL1GreenSlope (fun t => weightedGreenDecay t * g t) r +
      halfLineL1GreenSlope F r
  have hDer (r : ℝ) : HasDerivAt (innerGreenRepresentative g F) (slope r) r :=
    (hG.1 r).add (hS.1 r)
  refine ⟨fun r => (hDer r).differentiableAt, ?_⟩
  have heq : deriv (innerGreenRepresentative g F) = slope :=
    funext fun r => (hDer r).deriv
  rw [heq]
  exact hG.2.add hS.2

private theorem restore_c1
    (q : ℝ → ℝ) (a : ℝ)
    (hq : Differentiable ℝ q) (hdq : Continuous (deriv q)) :
    Differentiable ℝ (affineRestore q a) ∧
      Continuous (deriv (affineRestore q a)) := by
  have hm : Differentiable ℝ model :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).1
  have hdm : Continuous (deriv model) :=
    (contDiff_infty_iff_deriv.mp model_contDiff_infty).2.continuous
  have hDer (r : ℝ) : HasDerivAt (affineRestore q a)
      (deriv q r + a * deriv model r) r :=
    (hq r).hasDerivAt.add ((hm r).hasDerivAt.const_mul a)
  refine ⟨fun r => (hDer r).differentiableAt, ?_⟩
  have heq : deriv (affineRestore q a) =
      (fun r => deriv q r + a * deriv model r) :=
    funext fun r => (hDer r).deriv
  rw [heq]
  exact hdq.add (hdm.const_mul a)

private theorem physical_quotient_trace
    (q : ℝ → ℝ) (hq : Differentiable ℝ q)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => q t / t)
      ((r * deriv q r - q r) / r ^ 2) r := by
  simpa [mul_comm] using! ((hq r).hasDerivAt.div (hasDerivAt_id r) hr.ne')

/-- Canonical C1 representatives for the SAME conjugated physical source.
Exact Green identities, normalized Hilbert representatives and forced
affine charges are all present in the exported conclusion. -/
theorem actual_Hartree_conjugated_inner_C1_physical_traces
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let G := actualHartreeRadiallyConjugatedInnerSource
      (actualHartreeSlowInnerRadius ell) ell c z
    let gp : ℝ → ℝ := fun r => (G r).re
    let gm : ℝ → ℝ := fun r => (G r).im
    ∃ x : InnerCorrections, ∃ qp qm : ℝ → ℝ,
      (qp = affineRestore
        (innerGreenRepresentative
          (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
          (correctedPlusSource gp)) (actualPlusCharge gp)) ∧
      (qm = affineRestore
        (innerGreenRepresentative ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
          (correctedMinusSource gm)) (actualMinusCharge gm)) ∧
      (((x.1 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
        (fun r => weightedGreenDecay r *
          (qp r - actualPlusCharge gp * model r))) ∧
      (((x.2 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
        (fun r => weightedGreenDecay r *
          (qm r - actualMinusCharge gm * model r))) ∧
      InnerAffineProperties qp (actualPlusCharge gp) ∧
      InnerAffineProperties qm (actualMinusCharge gm) ∧
      (Differentiable ℝ qp ∧ Continuous (deriv qp)) ∧
      (Differentiable ℝ qm ∧ Continuous (deriv qm)) ∧
      (∀ r : ℝ, 0 < r →
        HasDerivAt (fun t : ℝ => qp t / t)
          ((r * deriv qp r - qp r) / r ^ 2) r ∧
        HasDerivAt (fun t : ℝ => qm t / t)
          ((r * deriv qm r - qm r) / r ^ 2) r) := by
  let G := actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z
  let gp : ℝ → ℝ := fun r => (G r).re
  let gm : ℝ → ℝ := fun r => (G r).im
  have hSource := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hPair := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) G hSource.1 hSource.2.1
  obtain ⟨x, hx⟩ := exists_actualInner_reconstructed
    (7 / 4 : ℝ) (by norm_num) (by norm_num) gp gm hPair.1 hPair.2
  dsimp only at hx
  rcases hx with ⟨hxp, hxm, hpp, hmp, _hpc, _hmc⟩
  let qp := innerGreenRepresentative
    (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
    (correctedPlusSource gp)
  let qm := innerGreenRepresentative
    ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
    (correctedMinusSource gm)
  have hpC1 : Differentiable ℝ qp ∧ Continuous (deriv qp) :=
    representative_c1_from_weighted _ (7 / 4 : ℝ) (by norm_num) _
      (correctedPlusSource_memWeightedL2
        (7 / 4 : ℝ) (by norm_num) gp hPair.1)
  have hmC1 : Differentiable ℝ qm ∧ Continuous (deriv qm) :=
    representative_c1_from_weighted _ (7 / 4 : ℝ) (by norm_num) _
      (correctedMinusSource_memWeightedL2
        (7 / 4 : ℝ) (by norm_num) gm hPair.2)
  have hpRest := restore_c1 qp (actualPlusCharge gp) hpC1.1 hpC1.2
  have hmRest := restore_c1 qm (actualMinusCharge gm) hmC1.1 hmC1.2
  refine ⟨x, affineRestore qp (actualPlusCharge gp),
    affineRestore qm (actualMinusCharge gm), rfl, rfl, ?_, ?_,
    affineRestore_properties qp _ hpp,
    affineRestore_properties qm _ hmp, hpRest, hmRest, ?_⟩
  · change (((x.1 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
      (fun r => weightedGreenDecay r *
        (affineRestore qp (actualPlusCharge gp) r - actualPlusCharge gp * model r)))
    simpa only [affineRestore, add_sub_cancel_right] using hxp
  · change (((x.2 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
      (fun r => weightedGreenDecay r *
        (affineRestore qm (actualMinusCharge gm) r - actualMinusCharge gm * model r)))
    simpa only [affineRestore, add_sub_cancel_right] using hxm
  · intro r hr
    exact ⟨physical_quotient_trace _ hpRest.1 r hr,
      physical_quotient_trace _ hmRest.1 r hr⟩

end HBL.TypeIIDynamicSelection
