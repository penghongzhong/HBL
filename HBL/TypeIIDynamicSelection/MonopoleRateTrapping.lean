import HBL.TypeIIDynamicSelection.MonopoleRateTail

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Once a genuine projected-source decay estimate is available, a strictly
positive initial modulation margin forces the OUTPUT limit to remain in
the physically admissible Type II range. No terminal speed is assigned. -/
theorem firstMonopoleDrivenMu_trapped
    {c b omega : ℝ → ℝ} {s0 beta A delta C : ℝ} (mu0 : ℝ)
    (hs0 : 0 < s0) (hbeta : 1 / 2 < beta) (hA : 0 ≤ A)
    (hdelta : 0 < delta)
    (hc : Differentiable ℝ c) (hb : Measurable b) (homega : Measurable omega)
    (hsmall : ∀ s : ℝ, s0 < s → |c s| ≤ 1)
    (hdecay : ∀ s : ℝ, s0 < s →
      |c s| ≤ A * s ^ (-beta) ∧ |deriv c s| ≤ A * s ^ (-1 - beta) ∧
      |b s| ≤ A * s ^ (-1 : ℝ) ∧ |omega s| ≤ A * s ^ (-1 : ℝ))
    (hsource : ∀ s : ℝ, s0 ≤ s →
      |firstMonopoleRealProjectedSource c b omega s| ≤
        C * s ^ (-1 - delta))
    (hmargin : (9 / 16 : ℝ) + C * (s0 ^ (-delta) / delta) < mu0) :
    (9 / 16 : ℝ) <
        firstMonopoleDrivenMuInfinity mu0 s0 c b omega ∧
      (1 / 2 : ℝ) <
        HBL.MainBackward.selectedPhysicalRate
          (firstMonopoleDrivenMuInfinity mu0 s0 c b omega) := by
  have htail := firstMonopoleDrivenMu_tail mu0 hs0 hbeta hA hdelta
    hc hb homega hsmall hdecay hsource s0 le_rfl
  have hbase :
      firstMonopoleDrivenMu mu0 s0 c b omega s0 = mu0 := by
    simp [firstMonopoleDrivenMu]
  rw [hbase] at htail
  have hpos : (9 / 16 : ℝ) <
      firstMonopoleDrivenMuInfinity mu0 s0 c b omega := by
    have hlower := (abs_le.mp htail).1
    linarith
  exact ⟨hpos, dynamically_selected_rate_super_self_similar _ hpos⟩

end HBL.TypeIIDynamicSelection
