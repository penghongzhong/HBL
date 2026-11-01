import HBL.KinematicTailEstimates
import Mathlib.Tactic

/-!
# Exact integrable gain from the original manuscript's physical flat-source window

The original one-layer proof has beta_- > 1/2 and a moving core exponent
  0 < rho_* < min(1/2, (5 beta_- - 2)/4).
Its actual spatially flat Hartree radiation has power
  s^(-5*betaMinus/2 + 2*rhoStar).
The strictly positive flat gain and complete time-tail integrability are
here derived, not supplied as external a priori decay assumptions.

This is the exact original epsilon_flat mechanism entering
  kappa_prof=min(delta,epsilon_flat,2 beta_- -1,1/2,rho_*) > 0.
The spatial flat-source estimate itself, actual PDE trajectory and true
one-layer Fredholm/Kummer/remote source gluing remain independent
mathematical obligations.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- The actual epsilon_flat exponent from manuscript eq:flat-integrable-stage3. -/
def actualHartreeFlatGain (beta rho : ℝ) : ℝ :=
  5 * beta / 2 - 2 * rho - 1

/-- The original admissible moving-core inequality gives a strictly
positive epsilon_flat, not merely a formal gain label. -/
theorem actual_Hartree_flat_gain_strict_pos
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hscale : rho < (5 * beta - 2) / 4) :
    0 < actualHartreeFlatGain beta rho := by
  have hpossible : 0 < 5 * beta - 2 := by linarith [hbeta]
  dsimp [actualHartreeFlatGain]
  linarith

/-- The original spatial source power is EXACTLY one full integrable
time power plus its PDE-relevant positive flat gain. -/
theorem actual_Hartree_flat_power_exact
    (beta rho : ℝ) :
    -5 * beta / 2 + 2 * rho =
      -1 - actualHartreeFlatGain beta rho := by
  unfold actualHartreeFlatGain
  ring

/-- The true original source decay exponent, whenever the actual
radial Hartree spatial bound has been established, is integrable on
the entire renormalized future and has the stated quantitative tail.
Neither its positivity nor the tail identity is assumed. -/
theorem actual_Hartree_flat_power_integrable_with_tail
    (beta rho s0 : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hscale : rho < (5 * beta - 2) / 4)
    (hs0 : 0 < s0) :
    IntegrableOn
      (fun s : ℝ => s ^ (-5 * beta / 2 + 2 * rho))
      (Ioi s0) ∧
    (∫ s in Ioi s0, s ^ (-5 * beta / 2 + 2 * rho)) =
      s0 ^ (-actualHartreeFlatGain beta rho) /
        actualHartreeFlatGain beta rho := by
  have hε :=
    actual_Hartree_flat_gain_strict_pos beta rho hbeta hrho hscale
  have he := actual_Hartree_flat_power_exact beta rho
  rw [he]
  constructor
  · exact integrableOn_Ioi_rpow_of_lt (by linarith) hs0
  · exact HBL.Kinematic.integral_Ioi_rpow_neg_one_sub hs0 hε

end HBL.TypeIIDynamicSelection
