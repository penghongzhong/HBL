import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedInnerC1Trace
import HBL.InnerReconstruction.RepresentativeFirstMomentTrace

/-!
Same-source quantitative physical traces of the canonical inner correction.
No free boundary jet is introduced: both Green reconstruction identities and
both a.e. identities with the normalized Hilbert solution are exported.
The constants are the ACTUAL first-moment bounds, including the potential
term of the Fredholm unknown. This does not yet prove uniform ell-smallness
of those constants, Kummer/remote compatibility or finite-profile closure.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Quantitative q/r traces of the SAME normalized physical reconstruction.
Mplus/Mminus are explicit actual integrals, not postulated small constants. -/
theorem actual_Hartree_conjugated_inner_canonical_moment_traces
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
      qp = affineRestore
        (innerGreenRepresentative
          (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
          (correctedPlusSource gp)) (actualPlusCharge gp) ∧
      qm = affineRestore
        (innerGreenRepresentative ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
          (correctedMinusSource gm)) (actualMinusCharge gm) ∧
      (((x.1 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
        (fun r => weightedGreenDecay r * (qp r - actualPlusCharge gp * model r))) ∧
      (((x.2 : RealL2 halfLineMeasure) : ℝ → ℝ) =ᵐ[halfLineMeasure]
        (fun r => weightedGreenDecay r * (qm r - actualMinusCharge gm * model r))) ∧
      InnerAffineProperties qp (actualPlusCharge gp) ∧
      InnerAffineProperties qm (actualMinusCharge gm) ∧
      (∀ r : ℝ, 2 < r →
        (|qp r / r - actualPlusCharge gp| ≤
          innerGreenBound (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
            (correctedPlusSource gp) / r ∧
         |deriv (fun t : ℝ => qp t / t) r| ≤
          innerGreenBound (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
            (correctedPlusSource gp) / r ^ 2) ∧
        (|qm r / r - actualMinusCharge gm| ≤
          innerGreenBound ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
            (correctedMinusSource gm) / r ∧
         |deriv (fun t : ℝ => qm t / t) r| ≤
          innerGreenBound ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
            (correctedMinusSource gm) / r ^ 2)) := by
  let G := actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z
  let gp : ℝ → ℝ := fun r => (G r).re
  let gm : ℝ → ℝ := fun r => (G r).im
  have hSource := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hPair := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) G hSource.1 hSource.2.1
  have hp := correctedPlusSource_memWeightedL2
    (7 / 4 : ℝ) (by norm_num) gp hPair.1
  have hm := correctedMinusSource_memWeightedL2
    (7 / 4 : ℝ) (by norm_num) gm hPair.2
  obtain ⟨x, qp, qm, hqp, hqm, hxp, hxm, hpA, hmA, _hpC, _hmC, _hDer⟩ :=
    actual_Hartree_conjugated_inner_C1_physical_traces
      ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  refine ⟨x, qp, qm, hqp, hqm, hxp, hxm, hpA, hmA, ?_⟩
  intro r hr
  constructor
  · rw [hqp]
    exact innerGreenRepresentative_affine_physical_trace_bounds
      (weightedPotentialOperator (x.1 : RealL2 halfLineMeasure))
      (7 / 4 : ℝ) (by norm_num) (correctedPlusSource gp) hp
      (actualPlusCharge gp) r hr
  · rw [hqm]
    exact innerGreenRepresentative_affine_physical_trace_bounds
      ((3 : ℝ) • (x.2 : RealL2 halfLineMeasure))
      (7 / 4 : ℝ) (by norm_num) (correctedMinusSource gm) hm
      (actualMinusCharge gm) r hr

end HBL.TypeIIDynamicSelection
