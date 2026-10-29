import HBL.MainRateSelection
import Mathlib.Tactic

/-!
# The rate is obtained from the actual rescaled clock, not prescribed

For a genuine Hartree modulation path, the physical remaining time tau and
scale lambda obey tau_s = -lambda^{-2} and lambda_s = b lambda.
The definitions q = tau lambda^2, mu = (2 b q - 1)/4 then force
q_s = 4 mu and b q = 1/2 + 2 mu.

These are unconditional *kinematic implications* from differentiated input
paths. They do not postulate a value of mu_infty and do not construct a PDE
solution. The actual projected Hartree modulation equation is still needed
to prove integrable drift and convergence of mu(s).
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def dynamicalClock (tau lambda : ℝ → ℝ) (s : ℝ) : ℝ :=
  tau s * lambda s ^ 2

def dynamicalMu (tau lambda b : ℝ → ℝ) (s : ℝ) : ℝ :=
  (2 * b s * dynamicalClock tau lambda s - 1) / 4

/-- Exact reconstructed-clock differential identity with an output mu(s). -/
theorem dynamicalClock_hasDerivAt
    (tau lambda b : ℝ → ℝ) (s : ℝ)
    (htau : HasDerivAt tau (-(lambda s)⁻¹ ^ 2) s)
    (hlambda : HasDerivAt lambda (b s * lambda s) s)
    (hln : lambda s ≠ 0) :
    HasDerivAt (dynamicalClock tau lambda)
      (4 * dynamicalMu tau lambda b s) s := by
  have h := htau.mul (hlambda.pow 2)
  convert h using 1
  · rfl
  · unfold dynamicalClock dynamicalMu
    field_simp [hln]
    ring

/-- Instantaneous logarithmic concentration exponent, determined from the
actual modulation coordinate and never from a prescribed final power. -/
theorem dynamical_rate_identity (tau lambda b : ℝ → ℝ) (s : ℝ) :
    b s * dynamicalClock tau lambda s =
      HBL.MainBackward.selectedPhysicalRate (dynamicalMu tau lambda b s) := by
  unfold dynamicalClock dynamicalMu HBL.MainBackward.selectedPhysicalRate
  ring

/-- The limit of the instantaneous exponent is the image of an observed
modulation limit, not an independently assigned speed. -/
theorem selected_rate_of_dynamical_mu_limit
    (mu : ℝ → ℝ) (muInf : ℝ)
    (hmu : Tendsto mu atTop (𝓝 muInf)) :
    Tendsto (fun s => HBL.MainBackward.selectedPhysicalRate (mu s))
      atTop (𝓝 (HBL.MainBackward.selectedPhysicalRate muInf)) := by
  have hc : Continuous HBL.MainBackward.selectedPhysicalRate :=
    HBL.MainBackward.selectedPhysicalRate_contDiff.continuous
  exact hc.continuousAt.tendsto.comp hmu

/-- Positivity of the *output* limit forces faster-than-self-similar
concentration. The positivity of that limit is a separate PDE obligation. -/
theorem dynamically_selected_rate_super_self_similar
    (muInf : ℝ) (hmu : (9 / 16 : ℝ) < muInf) :
    (1 / 2 : ℝ) < HBL.MainBackward.selectedPhysicalRate muInf := by
  unfold HBL.MainBackward.selectedPhysicalRate
  linarith

end HBL.TypeIIDynamicSelection
