import HBL.TypeIIDynamicSelection.MonopoleSourceTerminal

/-!
# First genuine source-driven instantaneous rate limit

The rate is the OUTPUT of integrating the actual Hartree-monopole
effective residual against the physically normalized threshold test.
No value of mu_infty or power exponent is supplied as an input.

This statement remains a result for the actual monopole approximate-profile
source. The final PDE profile, constrained centre and radiation feedback
have NOT been matched to these equations, so it is not the manuscript's
unconditional Type II blowup theorem.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- Integrable actual monopole-source projections select an instantaneous
concentration-rate limit, with the emergent rate expressed explicitly by
the primitive residual integral, not by a fixed target exponent. -/
theorem actual_monopole_source_selects_instantaneous_rate
    {c b omega : ℝ → ℝ} {s0 beta A : ℝ}
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ))
    (mu0 theta0 : ℝ) :
    ∃ muInf thetaInf : ℝ,
      muInf = mu0 +
        ∫ t in Ioi s0, monopoleThresholdCoordinatePlus c b omega t ∧
      thetaInf = theta0 +
        ∫ t in Ioi s0, monopoleThresholdCoordinateMinus c b omega t ∧
      Tendsto (fun s : ℝ =>
        HBL.MainBackward.selectedPhysicalRate
          (monopoleSourceDrivenMu c b omega s0 mu0 s))
        atTop (𝓝 (HBL.MainBackward.selectedPhysicalRate muInf)) ∧
      Tendsto (monopoleSourceDrivenTheta c b omega s0 theta0)
        atTop (𝓝 thetaInf) := by
  obtain ⟨muInf, thetaInf, hmuEq, hthetaEq, hmu, htheta⟩ :=
    actual_monopole_source_selects_terminal_coordinates hs0 hbeta hA
      hc hb homega hsmall hdecay mu0 theta0
  refine ⟨muInf, thetaInf, hmuEq, hthetaEq, ?_, htheta⟩
  exact selected_rate_of_dynamical_mu_limit
    (monopoleSourceDrivenMu c b omega s0 mu0) muInf hmu

end HBL.TypeIIDynamicSelection
