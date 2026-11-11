import Mathlib.Tactic

/-!
# Actual Hartree mass/phase transport: exact algebraic cancellation

These statements are the algebraic jet identities used when the SAME
original nonlocal Hartree PDE provides both its radial mass continuity
equation and its phase zero-mode Wronskian.

They DO NOT assert the existence of a strong nonlinear Hartree orbit,
differentiability of its moving interfaces, a mass conservation theorem,
or a time-decaying residual. Those analytic conditions are stated in
verification/HBL_213_ACTUAL_HARTREE_MOVING_BUBBLE_MASS_PHASE_FLUX_IDENTITY_20261110.md.

In particular, the renormalized bare scaling contribution to the
combined finite-radius phase/mass flux is an exact total derivative,
with only perturbation terms left on the right. No independent envelope,
Type-II rate, or new mathematical axiom is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

/-- The physical imaginary radial mass current decomposes into the
bubble-phase Wronskian and the genuine quadratic perturbation current. -/
theorem actual_Hartree_local_mass_phase_current_splits
    (B Br p pr q qr : ℝ) :
    (B + p) * qr - q * (Br + pr) =
      (B * qr - Br * q) + (p * qr - q * pr) := by
  ring

/-- Cancellation of the entire bare scaling resonance in the
renormalized physical mass/phase pairing, as a pointwise identity of
the actual real/imaginary C¹ radial jets.
Here Wr, pr, qr stand for the radial derivatives. -/
theorem actual_Hartree_renormalized_bare_scaling_phase_mass_jet_cancels
    (r W Wr p pr q qr : ℝ) :
    let rho := (W + p) ^ 2 + q ^ 2
    let rho_r := 2 * (W + p) * (Wr + pr) + 2 * q * qr
    let lambdaW := W / 2 + r * Wr
    let lambdaWp := (W + p) / 2 + r * (Wr + pr)
    r ^ 2 * (-W * lambdaWp + (rho + r * rho_r) / 2) =
      3 * r ^ 2 / 2 * (p ^ 2 + q ^ 2) +
      r ^ 3 * (p * pr + q * qr) +
      r ^ 2 * (lambdaW * p - (p ^ 2 + q ^ 2)) := by
  dsimp
  ring

/-- If the same physical solution produces the zero-mode Wronskian
flux and the local-mass transport identity, its explicit moving bubble
source moment cancels, leaving only the actual mass derivative, moving
endpoint, and nonlinear perturbation current. This is an algebraic
composition of two analytic identities; neither is assumed for an
unconstructed four-piece packet. -/
theorem actual_Hartree_same_orbit_phase_mass_source_cancels
    (flux bubbleSource remainingSource massDerivative endpoint quadraticCurrent : ℝ)
    (hWronskian :
      flux = -(bubbleSource + remainingSource))
    (hMass :
      massDerivative =
        -flux - quadraticCurrent - bubbleSource + endpoint) :
    remainingSource = massDerivative + quadraticCurrent - endpoint := by
  linarith

end HBL.TypeIIDynamicSelection
