import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Actual scalar nonautonomous unstable kernels.  Every kernel estimate is
derived from the integral of its coefficient.  The difference estimate keeps
the elapsed-time factor, which cannot be discarded in a pointwise relative
kernel bound over an unbounded time interval.  Identifying a coefficient with
the Hartree Hamiltonian growth mode remains a separate construction. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Shooting

/-- The actual backward kernel of the scalar equation y' = a y + f. -/
def unstableShootingKernel (a : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (-(∫ tau in s..t, a tau))

theorem unstableShootingKernel_pos (a : ℝ → ℝ) (s t : ℝ) :
    0 < unstableShootingKernel a s t := Real.exp_pos _

@[simp] theorem unstableShootingKernel_self (a : ℝ → ℝ) (s : ℝ) :
    unstableShootingKernel a s s = 1 := by
  simp [unstableShootingKernel]

/-- The cocycle law follows from addition of the actual interval integrals. -/
theorem unstableShootingKernel_cocycle {a : ℝ → ℝ} (ha : Continuous a)
    (s t u : ℝ) :
    unstableShootingKernel a s t * unstableShootingKernel a t u =
      unstableShootingKernel a s u := by
  unfold unstableShootingKernel
  rw [← Real.exp_add, ← neg_add,
    intervalIntegral.integral_add_adjacent_intervals
      (ha.intervalIntegrable s t) (ha.intervalIntegrable t u)]

/-- A fixed-base factorization for differentiating the actual terminal integral. -/
theorem unstableShootingKernel_factorization {a : ℝ → ℝ} (ha : Continuous a)
    (s0 s t : ℝ) :
    unstableShootingKernel a s t =
      Real.exp (∫ tau in s0..s, a tau) * unstableShootingKernel a s0 t := by
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (ha.intervalIntegrable s0 s) (ha.intervalIntegrable s t)
  unfold unstableShootingKernel
  rw [← Real.exp_add]
  congr 1
  linarith

/-- Genuine differentiation in the upper endpoint of the coefficient integral. -/
theorem unstableShootingKernel_hasDerivAt_right {a : ℝ → ℝ} (ha : Continuous a)
    (s t : ℝ) :
    HasDerivAt (unstableShootingKernel a s)
      (-a t * unstableShootingKernel a s t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (ha.intervalIntegrable s t)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  convert hi.neg.exp using 1
  · rfl
  · simp only [unstableShootingKernel, Pi.neg_apply]
    ring

/-- Genuine differentiation in the lower endpoint of the coefficient integral. -/
theorem unstableShootingKernel_hasDerivAt_left {a : ℝ → ℝ} (ha : Continuous a)
    (s t : ℝ) :
    HasDerivAt (fun x => unstableShootingKernel a x t)
      (a s * unstableShootingKernel a s t) s := by
  have hi := intervalIntegral.integral_hasDerivAt_left
    (ha.intervalIntegrable s t)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  convert hi.neg.exp using 1
  · rfl
  · simp only [unstableShootingKernel, Pi.neg_apply]
    ring

theorem unstableShootingKernel_continuous_right {a : ℝ → ℝ} (ha : Continuous a)
    (s : ℝ) : Continuous (unstableShootingKernel a s) :=
  continuous_iff_continuousAt.mpr
    (fun t => (unstableShootingKernel_hasDerivAt_right ha s t).continuousAt)

/-- A coefficient lower bound controls its true interval integral. -/
theorem unstableShootingCoefficient_integral_lower_bound
    {a : ℝ → ℝ} {s t e : ℝ} (hst : s ≤ t)
    (ha : ContinuousOn a (Icc s t))
    (hlower : ∀ tau ∈ Icc s t, e ≤ a tau) :
    e * (t - s) ≤ ∫ tau in s..t, a tau := by
  have hi := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => e) volume s t)
    (ha.intervalIntegrable_of_Icc hst) hlower
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi

/-- Exponential decay follows from the primitive coefficient bound; it is
not postulated as a property of an arbitrary kernel. -/
theorem unstableShootingKernel_le_exp {a : ℝ → ℝ} {s t e : ℝ}
    (hst : s ≤ t) (ha : ContinuousOn a (Icc s t))
    (hlower : ∀ tau ∈ Icc s t, e ≤ a tau) :
    unstableShootingKernel a s t ≤ Real.exp (-e * (t - s)) := by
  apply Real.exp_le_exp.mpr
  have hi := unstableShootingCoefficient_integral_lower_bound hst ha hlower
  linarith

private theorem exp_difference_below {x y m : ℝ} (hx : x ≤ m) (hy : y ≤ m) :
    |Real.exp x - Real.exp y| ≤ Real.exp m * |x - y| := by
  have hm := (convex_Iic m).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp)
    (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_exp.mpr hz) hy hx
  simpa only [Real.norm_eq_abs] using hm

/-- True kernel differences retain an elapsed-time factor.  The hypotheses
are only regularity and bounds on the two coefficient paths themselves. -/
theorem unstableShootingKernel_difference_bound
    {a b : ℝ → ℝ} {s t e D : ℝ} (hst : s ≤ t)
    (ha : ContinuousOn a (Icc s t)) (hb : ContinuousOn b (Icc s t))
    (halower : ∀ tau ∈ Icc s t, e ≤ a tau)
    (hblower : ∀ tau ∈ Icc s t, e ≤ b tau)
    (hdiff : ∀ tau ∈ Icc s t, |a tau - b tau| ≤ D) :
    |unstableShootingKernel a s t - unstableShootingKernel b s t| ≤
      D * (t - s) * Real.exp (-e * (t - s)) := by
  have haint : IntervalIntegrable a volume s t := ha.intervalIntegrable_of_Icc hst
  have hbint : IntervalIntegrable b volume s t := hb.intervalIntegrable_of_Icc hst
  have hA := unstableShootingCoefficient_integral_lower_bound hst ha halower
  have hB := unstableShootingCoefficient_integral_lower_bound hst hb hblower
  have hdiffint : |(∫ tau in s..t, a tau) - ∫ tau in s..t, b tau| ≤ D * (t - s) := by
    rw [← intervalIntegral.integral_sub haint hbint]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := t) (f := fun tau => a tau - b tau) (C := D) (by
        intro tau htau
        rw [uIoc_of_le hst] at htau
        rw [Real.norm_eq_abs]
        exact hdiff tau ⟨htau.1.le, htau.2⟩)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] using hi
  have hmean := exp_difference_below
    (x := -(∫ tau in s..t, a tau)) (y := -(∫ tau in s..t, b tau))
    (m := -e * (t - s)) (by linarith) (by linarith)
  have hneg : |-(∫ tau in s..t, a tau) - -(∫ tau in s..t, b tau)| =
      |(∫ tau in s..t, a tau) - ∫ tau in s..t, b tau| := by
    rw [neg_sub_neg, abs_sub_comm]
  rw [hneg] at hmean
  exact hmean.trans (by
    calc
      Real.exp (-e * (t - s)) *
          |(∫ tau in s..t, a tau) - ∫ tau in s..t, b tau| ≤
          Real.exp (-e * (t - s)) * (D * (t - s)) :=
        mul_le_mul_of_nonneg_left hdiffint (Real.exp_pos _).le
      _ = _ := by ring)

end HBL.Shooting
