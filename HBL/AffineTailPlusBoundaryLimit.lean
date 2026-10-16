import HBL.AffineTailHartreePairing

/-!
Far Wronskian of the scaling resonance in the real Hartree channel.

We obtain the derivative asymptotics from the exact identity
  psi_plus = r psi_minus' - psi_minus/2
and the already proven equation H_minus psi_minus=0. No nonlocal
H_plus zero-energy equation is assumed or asserted here.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- Derivative of the scale resonance reduced to the H-minus zero mode. -/
theorem resonancePlus_deriv_eq (r : ℝ) :
    deriv resonancePlus r =
      deriv resonanceMinus r / 2 +
        r * deriv (deriv resonanceMinus) r := by
  have hpsi : ContDiff ℝ ∞ resonanceMinus :=
    radialResonanceMinus_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonanceMinus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hD : HasDerivAt resonanceMinus (deriv resonanceMinus r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi).1 r).hasDerivAt
  have hDD : HasDerivAt (deriv resonanceMinus)
      (deriv (deriv resonanceMinus) r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi1).1 r).hasDerivAt
  have h :=
    ((hasDerivAt_id r).mul hDD).sub (hD.div_const 2)
  have heq : resonancePlus =
      (fun x : ℝ => x * deriv resonanceMinus x - resonanceMinus x / 2) := by
    funext x
    exact resonancePlus_eq_radius_deriv_sub_half x
  have hformula : deriv resonancePlus r =
      1 * deriv resonanceMinus r +
        id r * deriv (deriv resonanceMinus) r -
        deriv resonanceMinus r / 2 := by
    rw [heq]
    exact h.deriv
  rw [hformula]
  simp only [id_eq, one_mul]
  ring

/-- The explicit local Hartree potential satisfies R^2 V(R) -> 0. -/
theorem radius_sq_potential_tendsto_zero :
    Tendsto (fun R : ℝ => R ^ 2 * potential R)
      atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun R : ℝ => R⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hinv2 : Tendsto (fun R : ℝ => (R⁻¹) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hinv.pow 2
  have hnum : Tendsto (fun R : ℝ => 3 * (R⁻¹) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hinv2.const_mul 3
  have hden : Tendsto (fun R : ℝ => (1 + (R⁻¹) ^ 2) ^ 2)
      atTop (𝓝 (1 : ℝ)) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have hadd : Tendsto (fun R : ℝ => 1 + (R⁻¹) ^ 2)
        atTop (𝓝 (1 : ℝ)) := by
      simpa using hone.add hinv2
    simpa using hadd.pow 2
  have hrat : Tendsto
      (fun R : ℝ => (3 * (R⁻¹) ^ 2) / ((1 + (R⁻¹) ^ 2) ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    have h := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto
      (fun R : ℝ => (3 * (R⁻¹) ^ 2) / ((1 + (R⁻¹) ^ 2) ^ 2))
      atTop (𝓝 ((0 : ℝ) / 1)) at h
    simpa only [zero_div] using h
  apply hrat.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  have hne : R ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hR)
  have hpos : (1 + R ^ 2 : ℝ) ≠ 0 := by positivity
  have hposInv : (1 + (R⁻¹) ^ 2 : ℝ) ≠ 0 := by positivity
  unfold potential
  field_simp [hne, hpos, hposInv]
  ring

/-- The derivative of the scale resonance decays fast enough for Green's formula. -/
theorem radius_resonancePlus_deriv_tendsto_zero :
    Tendsto (fun R : ℝ => R * deriv resonancePlus R)
      atTop (𝓝 (0 : ℝ)) := by
  have hfirst : Tendsto
      (fun R : ℝ => (R * deriv resonanceMinus R) / 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using radius_resonanceMinus_deriv_tendsto_zero.div_const 2
  have hsecond : Tendsto
      (fun R : ℝ => -((R ^ 2 * potential R) * resonanceMinus R))
      atTop (𝓝 (0 : ℝ)) := by
    have h := radius_sq_potential_tendsto_zero.mul
      resonanceMinus_tendsto_one
    simpa using h.neg
  have hsum : Tendsto
      (fun R : ℝ =>
        (R * deriv resonanceMinus R) / 2 +
          -((R ^ 2 * potential R) * resonanceMinus R))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using hfirst.add hsecond
  apply hsum.congr'
  exact Filter.Eventually.of_forall (fun R : ℝ => by
    change (R * deriv resonanceMinus R) / 2 +
      -((R ^ 2 * potential R) * resonanceMinus R) =
      R * deriv resonancePlus R
    rw [resonancePlus_deriv_eq R]
    have hzero := hMinus_resonanceMinus_zero R
    change -deriv (deriv resonanceMinus) R -
      potential R * resonanceMinus R = 0 at hzero
    have hd : deriv (deriv resonanceMinus) R =
        -potential R * resonanceMinus R := by linarith
    rw [hd]
    ring)

/-- The real-channel Wronskian tends to -c-plus = +1/2. -/
theorem greenBoundary_plus_tendsto_half :
    Tendsto
      (fun R : ℝ =>
        greenBoundary resonancePlus (deriv resonancePlus)
          model (deriv model) R)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlim :
      Tendsto
        (fun R : ℝ =>
          -resonancePlus R + R * deriv resonancePlus R)
        atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := resonancePlus_tendsto_neg_half.neg.add
      radius_resonancePlus_deriv_tendsto_zero
    simpa using h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with R hR
  exact (greenBoundary_plus_far R hR).symm

end HBL.Modulation.AffineTail
