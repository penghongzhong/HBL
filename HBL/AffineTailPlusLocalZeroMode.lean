import HBL.AffineTailPotentialDerivative

/-!
Exact differential part of H-plus applied to the radial scaling resonance.

For a local potential V with psi_minus''=-V psi_minus, differentiation of
psi_plus = r psi_minus' - psi_minus/2 gives the identity
  (-d^2-3V)psi_plus = 3V psi_minus + r V' psi_minus - 2r V psi_minus'.
The real-channel zero-mode problem is therefore reduced to precisely one
nonlocal integral formula.  That remaining formula is an explicit analytic obligation.
-/

noncomputable section

open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

theorem resonancePlus_second_from_minus (r : ℝ) :
    deriv (deriv resonancePlus) r =
      -(3 / 2 : ℝ) * potential r * resonanceMinus r -
      r * potentialDerivative r * resonanceMinus r -
      r * potential r * deriv resonanceMinus r := by
  have hpsi : ContDiff ℝ ∞ resonanceMinus :=
    radialResonanceMinus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonanceMinus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hD : HasDerivAt resonanceMinus (deriv resonanceMinus r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi).1 r).hasDerivAt
  have hDD : HasDerivAt (deriv resonanceMinus)
      (-potential r * resonanceMinus r) r := by
    have h := ((contDiff_infty_iff_deriv.mp hpsi1).1 r).hasDerivAt
    rw [resonanceMinus_second_eq_potential r] at h
    exact h
  have hmul := (hasDerivAt_id r).mul
    ((potential_hasDerivAt r).mul hD)
  have h := (hDD.div_const 2).sub hmul
  have hfun : deriv resonancePlus =
      fun x : ℝ => deriv resonanceMinus x / 2 -
        x * (potential x * resonanceMinus x) := by
    funext x
    rw [resonancePlus_deriv_from_minus]
    ring
  rw [hfun]
  convert h.deriv using 1
  · funext x
    ring
  · ring

/-- Fully checked local real-channel residual before applying the Hartree
nonlocal operator. No unproved integral identity enters this result. -/
theorem hPlus_local_on_scale (r : ℝ) :
    -deriv (deriv resonancePlus) r -
      3 * potential r * resonancePlus r =
      3 * potential r * resonanceMinus r +
      r * potentialDerivative r * resonanceMinus r -
      2 * r * potential r * deriv resonanceMinus r := by
  rw [resonancePlus_second_from_minus,
    resonancePlus_eq_radius_deriv_sub_half]
  ring

/-- A precise analytical obstruction: establishing the displayed
nonlocal integral identity on positive radii implies the exact Hartree
scale zero mode, without any additional abstract spectral hypothesis. -/
theorem hPlus_zero_of_nonlocal_formula
    (hT : ∀ r : ℝ, 0 < r →
      nonlocalApply resonancePlus r =
        3 * potential r * resonanceMinus r +
        r * potentialDerivative r * resonanceMinus r -
        2 * r * potential r * deriv resonanceMinus r) :
    ∀ r : ℝ, 0 < r → hPlusApply resonancePlus r = 0 := by
  intro r hr
  unfold hPlusApply
  rw [hPlus_local_on_scale, hT r hr]
  ring

end HBL.Modulation.AffineTail
