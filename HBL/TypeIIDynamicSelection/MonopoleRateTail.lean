import HBL.TypeIIDynamicSelection.MonopoleRateLimit

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Modulation.Monopole

/-- A bound for the *actual* first-monopole Hartree projected source
immediately gives a quantitative emergent-rate tail. The displayed
source pointwise decay is an explicit outstanding analytic hypothesis:
the strict integral is already known to exist from the constructed
physical radial cutoff projection, but the full PDE must still be matched. -/
theorem firstMonopoleDrivenMu_tail
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
    (s : ℝ) (hs : s0 ≤ s) :
    |firstMonopoleDrivenMuInfinity mu0 s0 c b omega -
        firstMonopoleDrivenMu mu0 s0 c b omega s| ≤
      C * (s ^ (-delta) / delta) := by
  have hspos : 0 < s := hs0.trans_le hs
  have hi : IntegrableOn
      (firstMonopoleRealProjectedSource c b omega) (Ioi s0) :=
    (monopoleThresholdCoordinates_integrable
      hs0 hbeta hA hc hb homega hsmall hdecay).2.1
  have hit : IntegrableOn
      (firstMonopoleRealProjectedSource c b omega) (Ioi s) :=
    hi.mono_set (Ioi_subset_Ioi hs)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have hiden :
      firstMonopoleDrivenMuInfinity mu0 s0 c b omega -
        firstMonopoleDrivenMu mu0 s0 c b omega s =
        ∫ t in Ioi s, firstMonopoleRealProjectedSource c b omega t := by
    dsimp [firstMonopoleDrivenMuInfinity, firstMonopoleDrivenMu]
    linarith
  have hpower : IntegrableOn (fun t : ℝ => C * t ^ (-1 - delta)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt
      (show -1 - delta < -1 by linarith) hspos).const_mul C
  rw [hiden]
  calc
    |∫ t in Ioi s, firstMonopoleRealProjectedSource c b omega t| ≤
        ∫ t in Ioi s, |firstMonopoleRealProjectedSource c b omega t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi s, C * t ^ (-1 - delta) := by
      apply integral_mono_ae hit.abs hpower
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hsource t (hs.trans ht.le)
    _ = C * (s ^ (-delta) / delta) := by
      rw [integral_const_mul, HBL.Kinematic.integral_Ioi_rpow_neg_one_sub hspos hdelta]

end HBL.TypeIIDynamicSelection
