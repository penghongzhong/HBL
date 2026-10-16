import HBL.AffineTailMinusAsymptotics

/-!
Exact finite-radius threshold-charge Green formula in the H-minus channel.

Unlike the original manuscript's finite-radius H-plus formula, no nonlocal
commutator arises in H-minus.  The proof below verifies all differentiation
and interval integrability hypotheses for the concrete smooth Hartree
resonance and affine cutoff.  It then obtains the far-radius limit from the
already kernel-verified Wronskian asymptotics.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- Fully concrete finite-interval Green formula in the imaginary channel. -/
theorem hMinus_charge_finite (R : ℝ) :
    (∫ r in (0 : ℝ)..R,
      resonanceMinus r * hMinusApply model r) =
      greenBoundary resonanceMinus (deriv resonanceMinus)
        model (deriv model) R := by
  have hpsi : ContDiff ℝ ∞ resonanceMinus :=
    radialResonanceMinus_contDiff_infty
  have hq : ContDiff ℝ ∞ model := model_contDiff_infty
  have hpsi1 : ContDiff ℝ ∞ (deriv resonanceMinus) :=
    (contDiff_infty_iff_deriv.mp hpsi).2
  have hpsi2 : ContDiff ℝ ∞ (deriv (deriv resonanceMinus)) :=
    (contDiff_infty_iff_deriv.mp hpsi1).2
  have hq1 : ContDiff ℝ ∞ (deriv model) :=
    (contDiff_infty_iff_deriv.mp hq).2
  have hq2 : ContDiff ℝ ∞ (deriv (deriv model)) :=
    (contDiff_infty_iff_deriv.mp hq1).2
  have hpBase : Continuous (fun r : ℝ => 1 + r ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hpNZ (r : ℝ) : ((1 + r ^ 2) ^ 2 : ℝ) ≠ 0 := by
    positivity
  have hp : Continuous potential := by
    unfold potential
    exact continuous_const.div (hpBase.pow 2) hpNZ
  have hlocCont :
      Continuous (fun r : ℝ =>
        resonanceMinus r *
          ((-deriv (deriv model) r) - potential r * model r) -
        (((-deriv (deriv resonanceMinus) r) -
          potential r * resonanceMinus r) * model r)) :=
    (hpsi.continuous.mul
      (hq2.continuous.neg.sub (hp.mul hq.continuous))).sub
      ((hpsi2.continuous.neg.sub (hp.mul hpsi.continuous)).mul
        hq.continuous)
  have hlocInt : IntervalIntegrable
      (fun r : ℝ =>
        resonanceMinus r *
          ((-deriv (deriv model) r) - potential r * model r) -
        (((-deriv (deriv resonanceMinus) r) -
          potential r * resonanceMinus r) * model r))
      volume 0 R :=
    hlocCont.intervalIntegrable 0 R
  have hpsiD (r : ℝ) :
      HasDerivAt resonanceMinus (deriv resonanceMinus r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi).1 r).hasDerivAt
  have hpsiDD (r : ℝ) :
      HasDerivAt (deriv resonanceMinus)
        (deriv (deriv resonanceMinus) r) r :=
    ((contDiff_infty_iff_deriv.mp hpsi1).1 r).hasDerivAt
  have hqD (r : ℝ) : HasDerivAt model (deriv model r) r :=
    ((contDiff_infty_iff_deriv.mp hq).1 r).hasDerivAt
  have hqDD (r : ℝ) :
      HasDerivAt (deriv model) (deriv (deriv model) r) r :=
    ((contDiff_infty_iff_deriv.mp hq1).1 r).hasDerivAt
  have hrewrite :
      (fun r : ℝ =>
        resonanceMinus r *
          ((-deriv (deriv model) r) - potential r * model r) -
        (((-deriv (deriv resonanceMinus) r) -
          potential r * resonanceMinus r) * model r)) =
      (fun r : ℝ => resonanceMinus r * hMinusApply model r) := by
    funext r
    have hz := hMinus_resonanceMinus_zero r
    change -deriv (deriv resonanceMinus) r -
      potential r * resonanceMinus r = 0 at hz
    simp only [hMinusApply, hz, zero_mul, sub_zero]
  have hmain := green_localSchrodinger (0 : ℝ) R potential
    resonanceMinus (deriv resonanceMinus)
    (deriv (deriv resonanceMinus))
    model (deriv model) (deriv (deriv model))
    hpsiD hpsiDD hqD hqDD hlocInt
  rw [hrewrite] at hmain
  simpa only [greenBoundary_minus_at_zero, sub_zero] using hmain

/-- The original integral over [0,R] has the exact limit -c_minus=-1. -/
theorem hMinus_charge_interval_tendsto_neg_one :
    Tendsto
      (fun R : ℝ =>
        ∫ r in (0 : ℝ)..R,
          resonanceMinus r * hMinusApply model r)
      atTop (𝓝 (-1 : ℝ)) := by
  exact greenBoundary_minus_tendsto_neg_one.congr'
    (Filter.Eventually.of_forall
      (fun R : ℝ => (hMinus_charge_finite R).symm))

end HBL.Modulation.AffineTail
