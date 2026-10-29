import HBL.TypeIIDynamicSelection.MonopoleRateDefinitions

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole

/-- The first-order Hartree monopole threshold projection generates an
actual scalar limit; its numerical value is never prescribed in advance.
This theorem applies to the physical first-monopole source, not to the
unconstructed full Hartree blowup modulation equation. -/
theorem firstMonopoleDrivenMu_tendsto
    {c b omega : ℝ → ℝ} {s0 beta A : ℝ} (mu0 : ℝ)
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ)) :
    Tendsto (firstMonopoleDrivenMu mu0 s0 c b omega) atTop
      (𝓝 (firstMonopoleDrivenMuInfinity mu0 s0 c b omega)) := by
  have hint : IntegrableOn
      (firstMonopoleRealProjectedSource c b omega) (Ioi s0) :=
    (monopoleThresholdCoordinates_integrable
      hs0 hbeta hA hc hb homega hsmall hdecay).2.1
  have ht := intervalIntegral_tendsto_integral_Ioi s0 hint
    (tendsto_id : Tendsto (fun s : ℝ => s) atTop atTop)
  have ha := (tendsto_const_nhds (x := mu0)).add ht
  change Tendsto (fun s : ℝ => mu0 + ∫ t in s0..s,
      firstMonopoleRealProjectedSource c b omega t) atTop
    (𝓝 (mu0 + ∫ t in Ioi s0, firstMonopoleRealProjectedSource c b omega t))
  simpa only [id_eq] using ha

end HBL.TypeIIDynamicSelection
