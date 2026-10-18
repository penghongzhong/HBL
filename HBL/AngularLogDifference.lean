import HBL.LogSinFourierCoefficient
import HBL.FourierParsevalCross

/-!
Fourier coefficients of the angular logarithmic Hartree kernel.

We first work with the globally periodic representative `log |sin x|`.
This keeps every translation across an endpoint literal and postpones the
removal of the diagonal (a null set) to the operator-kernel step.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval ComplexConjugate

namespace HBL

def logAbsSin (x : ℝ) : ℝ := Real.log |Real.sin x|

def angularLogDifference (theta s : ℝ) : ℝ :=
  logAbsSin (theta + s) - logAbsSin (theta - s)

theorem logAbsSin_eq_log_sin (x : ℝ) :
    logAbsSin x = Real.log (Real.sin x) := by
  simp [logAbsSin, Real.log_abs]

theorem logAbsSin_periodic : Function.Periodic logAbsSin Real.pi := by
  intro x
  simp [logAbsSin, Real.sin_add_pi]

theorem logAbsSin_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable logAbsSin volume a b := by
  refine (intervalIntegrable_log_sin (a := a) (b := b)).congr ?_
  intro x _
  exact (logAbsSin_eq_log_sin x).symm

theorem cos_two_nat_periodic (n : ℕ) :
    Function.Periodic (fun x : ℝ => Real.cos (2 * n * x)) Real.pi := by
  intro x
  change Real.cos (2 * (n : ℝ) * (x + Real.pi)) =
    Real.cos (2 * (n : ℝ) * x)
  rw [show 2 * (n : ℝ) * (x + Real.pi) =
      2 * n * x + n * (2 * Real.pi) by ring]
  exact Real.cos_add_nat_mul_two_pi _ n

theorem sin_two_nat_periodic (n : ℕ) :
    Function.Periodic (fun x : ℝ => Real.sin (2 * n * x)) Real.pi := by
  intro x
  change Real.sin (2 * (n : ℝ) * (x + Real.pi)) =
    Real.sin (2 * (n : ℝ) * x)
  rw [show 2 * (n : ℝ) * (x + Real.pi) =
      2 * n * x + n * (2 * Real.pi) by ring]
  exact Real.sin_add_nat_mul_two_pi _ n

theorem logAbsSin_mul_cos_periodic (n : ℕ) :
    Function.Periodic
      (fun x : ℝ => logAbsSin x * Real.cos (2 * n * x)) Real.pi :=
  logAbsSin_periodic.mul (cos_two_nat_periodic n)

theorem logAbsSin_mul_sin_periodic (n : ℕ) :
    Function.Periodic
      (fun x : ℝ => logAbsSin x * Real.sin (2 * n * x)) Real.pi :=
  logAbsSin_periodic.mul (sin_two_nat_periodic n)

theorem integral_logAbsSin_mul_cos_two_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in 0..Real.pi,
      logAbsSin x * Real.cos (2 * n * x)) =
        -(Real.pi / (2 * n)) := by
  simpa only [logAbsSin_eq_log_sin] using
    integral_log_sin_mul_cos_two_nat n hn

theorem integral_logAbsSin_mul_sin_two_nat (n : ℕ) :
    (∫ x : ℝ in 0..Real.pi,
      logAbsSin x * Real.sin (2 * n * x)) = 0 := by
  let q : ℝ → ℝ := fun x => logAbsSin x * Real.sin (2 * n * x)
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := Real.pi) q Real.pi
  have hpoint : ∀ x : ℝ, q (Real.pi - x) = -q x := by
    intro x
    have hlog : logAbsSin (Real.pi - x) = logAbsSin x := by
      simp [logAbsSin, Real.sin_pi_sub]
    have hsin : Real.sin (2 * (n : ℝ) * (Real.pi - x)) =
        -Real.sin (2 * n * x) := by
      rw [show 2 * (n : ℝ) * (Real.pi - x) =
        n * (2 * Real.pi) - 2 * n * x by ring]
      exact Real.sin_nat_mul_two_pi_sub (2 * n * x) n
    simp only [q, hlog, hsin]
    ring
  have hneg :
      (∫ x : ℝ in 0..Real.pi, q (Real.pi - x)) =
        -(∫ x : ℝ in 0..Real.pi, q x) := by
    calc
      (∫ x : ℝ in 0..Real.pi, q (Real.pi - x)) =
          ∫ x : ℝ in 0..Real.pi, -q x := by
            apply intervalIntegral.integral_congr
            intro x _
            exact hpoint x
      _ = -(∫ x : ℝ in 0..Real.pi, q x) :=
        intervalIntegral.integral_neg
  change (∫ x : ℝ in 0..Real.pi, q x) = 0
  have hreflect' :
      (∫ x : ℝ in 0..Real.pi, q (Real.pi - x)) =
        ∫ x : ℝ in 0..Real.pi, q x := by
    simpa using hreflect
  rw [hneg] at hreflect'
  linarith

theorem integral_logAbsSin_mul_cos_period
    (a : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in a..a + Real.pi,
      logAbsSin x * Real.cos (2 * n * x)) =
        -(Real.pi / (2 * n)) := by
  rw [(logAbsSin_mul_cos_periodic n).intervalIntegral_add_eq a 0]
  simpa using integral_logAbsSin_mul_cos_two_nat n hn

theorem integral_logAbsSin_mul_sin_period (a : ℝ) (n : ℕ) :
    (∫ x : ℝ in a..a + Real.pi,
      logAbsSin x * Real.sin (2 * n * x)) = 0 := by
  rw [(logAbsSin_mul_sin_periodic n).intervalIntegral_add_eq a 0]
  simpa using integral_logAbsSin_mul_sin_two_nat n

theorem intervalIntegrable_logAbsSin_mul_cos
    (a b : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ => logAbsSin x * Real.cos (2 * n * x))
      volume a b := by
  exact (logAbsSin_intervalIntegrable a b).mul_continuousOn
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_const |>.mul continuous_id)).continuousOn)

theorem intervalIntegrable_logAbsSin_mul_sin
    (a b : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ => logAbsSin x * Real.sin (2 * n * x))
      volume a b := by
  exact (logAbsSin_intervalIntegrable a b).mul_continuousOn
    ((Real.continuous_sin.comp
      (continuous_const.mul continuous_const |>.mul continuous_id)).continuousOn)

theorem integral_logAbsSin_add_mul_sin
    (theta : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫ s : ℝ in 0..Real.pi,
      logAbsSin (theta + s) * Real.sin (2 * n * s)) =
        Real.pi / (2 * n) * Real.sin (2 * n * theta) := by
  let q : ℝ → ℝ := fun x =>
    logAbsSin x * Real.sin (2 * n * (x - theta))
  have hshift := intervalIntegral.integral_comp_add_right
    (a := (0 : ℝ)) (b := Real.pi) q theta
  have hshift' :
      (∫ s : ℝ in 0..Real.pi,
        logAbsSin (theta + s) * Real.sin (2 * n * s)) =
      ∫ x : ℝ in theta..theta + Real.pi,
        logAbsSin x * Real.sin (2 * n * (x - theta)) := by
    calc
      (∫ s : ℝ in 0..Real.pi,
          logAbsSin (theta + s) * Real.sin (2 * n * s)) =
          ∫ s : ℝ in 0..Real.pi, q (s + theta) := by
            apply intervalIntegral.integral_congr
            intro s _
            dsimp [q]
            congr 2
            · ring
            · congr 1
              ring
      _ = ∫ x : ℝ in theta..Real.pi + theta, q x := by
        simpa only [zero_add] using hshift
      _ = ∫ x : ℝ in theta..theta + Real.pi,
          logAbsSin x * Real.sin (2 * n * (x - theta)) := by
            rw [add_comm Real.pi theta]
  rw [hshift']
  have hs := intervalIntegrable_logAbsSin_mul_sin
    theta (theta + Real.pi) n
  have hc := intervalIntegrable_logAbsSin_mul_cos
    theta (theta + Real.pi) n
  calc
    (∫ x : ℝ in theta..theta + Real.pi,
        logAbsSin x * Real.sin (2 * n * (x - theta))) =
        ∫ x : ℝ in theta..theta + Real.pi,
          ((logAbsSin x * Real.sin (2 * n * x)) *
              Real.cos (2 * n * theta) -
            (logAbsSin x * Real.cos (2 * n * x)) *
              Real.sin (2 * n * theta)) := by
          apply intervalIntegral.integral_congr
          intro x _
          change logAbsSin x * Real.sin (2 * (n : ℝ) * (x - theta)) = _
          rw [show 2 * (n : ℝ) * (x - theta) =
            2 * n * x - 2 * n * theta by ring, Real.sin_sub]
          ring
    _ = (∫ x : ℝ in theta..theta + Real.pi,
          logAbsSin x * Real.sin (2 * n * x)) *
            Real.cos (2 * n * theta) -
        (∫ x : ℝ in theta..theta + Real.pi,
          logAbsSin x * Real.cos (2 * n * x)) *
            Real.sin (2 * n * theta) := by
          rw [intervalIntegral.integral_sub
            (hs.mul_const _) (hc.mul_const _),
            intervalIntegral.integral_mul_const,
            intervalIntegral.integral_mul_const]
    _ = Real.pi / (2 * n) * Real.sin (2 * n * theta) := by
      rw [integral_logAbsSin_mul_sin_period theta n,
        integral_logAbsSin_mul_cos_period theta n hn]
      ring

theorem integral_logAbsSin_sub_mul_sin
    (theta : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫ s : ℝ in 0..Real.pi,
      logAbsSin (theta - s) * Real.sin (2 * n * s)) =
        -(Real.pi / (2 * n) * Real.sin (2 * n * theta)) := by
  let q : ℝ → ℝ := fun x =>
    logAbsSin x * Real.sin (2 * n * (theta - x))
  have hshift := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := Real.pi) q theta
  have hshift' :
      (∫ s : ℝ in 0..Real.pi,
        logAbsSin (theta - s) * Real.sin (2 * n * s)) =
      ∫ x : ℝ in theta - Real.pi..theta,
        logAbsSin x * Real.sin (2 * n * (theta - x)) := by
    calc
      (∫ s : ℝ in 0..Real.pi,
          logAbsSin (theta - s) * Real.sin (2 * n * s)) =
          ∫ s : ℝ in 0..Real.pi, q (theta - s) := by
            apply intervalIntegral.integral_congr
            intro s _
            dsimp [q]
            congr 2
            congr 1
            ring
      _ = ∫ x : ℝ in theta - Real.pi..theta - 0, q x := hshift
      _ = ∫ x : ℝ in theta - Real.pi..theta,
          logAbsSin x * Real.sin (2 * n * (theta - x)) := by simp [q]
  rw [hshift']
  have hs := intervalIntegrable_logAbsSin_mul_sin
    (theta - Real.pi) theta n
  have hc := intervalIntegrable_logAbsSin_mul_cos
    (theta - Real.pi) theta n
  calc
    (∫ x : ℝ in theta - Real.pi..theta,
        logAbsSin x * Real.sin (2 * n * (theta - x))) =
        ∫ x : ℝ in theta - Real.pi..theta,
          ((logAbsSin x * Real.cos (2 * n * x)) *
              Real.sin (2 * n * theta) -
            (logAbsSin x * Real.sin (2 * n * x)) *
              Real.cos (2 * n * theta)) := by
          apply intervalIntegral.integral_congr
          intro x _
          change logAbsSin x * Real.sin (2 * (n : ℝ) * (theta - x)) = _
          rw [show 2 * (n : ℝ) * (theta - x) =
            2 * n * theta - 2 * n * x by ring, Real.sin_sub]
          ring
    _ = (∫ x : ℝ in theta - Real.pi..theta,
          logAbsSin x * Real.cos (2 * n * x)) *
            Real.sin (2 * n * theta) -
        (∫ x : ℝ in theta - Real.pi..theta,
          logAbsSin x * Real.sin (2 * n * x)) *
            Real.cos (2 * n * theta) := by
          rw [intervalIntegral.integral_sub
            (hc.mul_const _) (hs.mul_const _),
            intervalIntegral.integral_mul_const,
            intervalIntegral.integral_mul_const]
    _ = -(Real.pi / (2 * n) * Real.sin (2 * n * theta)) := by
      have hcos :
          (∫ x : ℝ in theta - Real.pi..theta,
            logAbsSin x * Real.cos (2 * n * x)) =
              -(Real.pi / (2 * n)) := by
        simpa only [sub_add_cancel] using
          integral_logAbsSin_mul_cos_period (theta - Real.pi) n hn
      have hsin :
          (∫ x : ℝ in theta - Real.pi..theta,
            logAbsSin x * Real.sin (2 * n * x)) = 0 := by
        simpa only [sub_add_cancel] using
          integral_logAbsSin_mul_sin_period (theta - Real.pi) n
      rw [hcos, hsin]
      ring

theorem integral_angularLogDifference_mul_sin
    (theta : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫ s : ℝ in 0..Real.pi,
      angularLogDifference theta s * Real.sin (2 * n * s)) =
        Real.pi / n * Real.sin (2 * n * theta) := by
  have hp := integral_logAbsSin_add_mul_sin theta n hn
  have hm := integral_logAbsSin_sub_mul_sin theta n hn
  have hip : IntervalIntegrable
      (fun s : ℝ => logAbsSin (theta + s) * Real.sin (2 * n * s))
      volume 0 Real.pi := by
    have hlog : IntervalIntegrable
        (fun s : ℝ => logAbsSin (s + theta)) volume 0 Real.pi := by
      simpa only [sub_self, add_sub_cancel_left] using
        (logAbsSin_intervalIntegrable theta
          (theta + Real.pi)).comp_add_right theta
    have hsincont : Continuous
        (fun s : ℝ => Real.sin (2 * (n : ℝ) * s)) := by fun_prop
    have hmul := hlog.mul_continuousOn hsincont.continuousOn
    simpa only [add_comm theta] using hmul
  have him : IntervalIntegrable
      (fun s : ℝ => logAbsSin (theta - s) * Real.sin (2 * n * s))
      volume 0 Real.pi := by
    have hlog : IntervalIntegrable
        (fun s : ℝ => logAbsSin (theta - s)) volume 0 Real.pi := by
      simpa only [sub_self, sub_sub_cancel] using
        (logAbsSin_intervalIntegrable theta
          (theta - Real.pi)).comp_sub_left theta
    exact hlog.mul_continuousOn
      ((Real.continuous_sin.comp
        (continuous_const.mul continuous_const |>.mul continuous_id)).continuousOn)
  simp only [angularLogDifference, sub_mul]
  rw [intervalIntegral.integral_sub hip him, hp, hm]
  field_simp
  ring

theorem angularLogDifference_reflect (theta s : ℝ) :
    angularLogDifference theta (Real.pi - s) =
      -angularLogDifference theta s := by
  have hplus :
      logAbsSin (theta + (Real.pi - s)) = logAbsSin (theta - s) := by
    have h := logAbsSin_periodic (theta - s)
    convert h using 1 <;> ring
  have hminus :
      logAbsSin (theta - (Real.pi - s)) = logAbsSin (theta + s) := by
    have h := logAbsSin_periodic (theta + s - Real.pi)
    convert h.symm using 1 <;> ring
  rw [angularLogDifference, angularLogDifference, hplus, hminus]
  ring

theorem integral_angularLogDifference_mul_cos
    (theta : ℝ) (n : ℕ) :
    (∫ s : ℝ in 0..Real.pi,
      angularLogDifference theta s * Real.cos (2 * n * s)) = 0 := by
  let q : ℝ → ℝ := fun s =>
    angularLogDifference theta s * Real.cos (2 * n * s)
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := Real.pi) q Real.pi
  have hpoint : ∀ s : ℝ, q (Real.pi - s) = -q s := by
    intro s
    have hcos : Real.cos (2 * (n : ℝ) * (Real.pi - s)) =
        Real.cos (2 * n * s) := by
      rw [show 2 * (n : ℝ) * (Real.pi - s) =
        n * (2 * Real.pi) - 2 * n * s by ring]
      exact Real.cos_nat_mul_two_pi_sub (2 * n * s) n
    simp only [q, angularLogDifference_reflect, hcos]
    ring
  have hneg :
      (∫ s : ℝ in 0..Real.pi, q (Real.pi - s)) =
        -(∫ s : ℝ in 0..Real.pi, q s) := by
    calc
      (∫ s : ℝ in 0..Real.pi, q (Real.pi - s)) =
          ∫ s : ℝ in 0..Real.pi, -q s := by
            apply intervalIntegral.integral_congr
            intro s _
            exact hpoint s
      _ = -(∫ s : ℝ in 0..Real.pi, q s) :=
        intervalIntegral.integral_neg
  change (∫ s : ℝ in 0..Real.pi, q s) = 0
  have hreflect' :
      (∫ s : ℝ in 0..Real.pi, q (Real.pi - s)) =
        ∫ s : ℝ in 0..Real.pi, q s := by
    simpa using hreflect
  rw [hneg] at hreflect'
  linarith

def angularLogDifferenceC (theta s : ℝ) : ℂ :=
  angularLogDifference theta s

theorem fourier_neg_nat_on_pi (n : ℕ) (x : ℝ) :
    fourier (-(n : ℤ)) (x : AddCircle Real.pi) =
      (Real.cos (2 * n * x) : ℂ) -
        Complex.I * (Real.sin (2 * n * x) : ℂ) := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * -(n : ℂ) * (x : ℂ) /
          (Real.pi : ℂ) =
        (-(2 * (n : ℝ) * x) : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  rw [Int.cast_neg, Int.cast_natCast, harg, Complex.exp_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

theorem fourier_neg_nat_on_pi_sub_zero (n : ℕ) (x : ℝ) :
    fourier (-(n : ℤ)) (x : AddCircle (Real.pi - 0)) =
      (Real.cos (2 * n * x) : ℂ) -
        Complex.I * (Real.sin (2 * n * x) : ℂ) := by
  rw [fourier_coe_apply, Int.cast_neg, Int.cast_natCast]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * -(n : ℂ) * (x : ℂ) /
          ((Real.pi - 0 : ℝ) : ℂ) =
        (-(2 * (n : ℝ) * x) : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  rw [harg, Complex.exp_mul_I]
  simp
  ring

theorem fourier_pos_nat_on_pi_sub_zero (n : ℕ) (x : ℝ) :
    fourier (n : ℤ) (x : AddCircle (Real.pi - 0)) =
      (Real.cos (2 * n * x) : ℂ) +
        Complex.I * (Real.sin (2 * n * x) : ℂ) := by
  rw [fourier_coe_apply, Int.cast_natCast]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) /
          ((Real.pi - 0 : ℝ) : ℂ) =
        ((2 * (n : ℝ) * x) : ℂ) * Complex.I := by
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  rw [harg, Complex.exp_mul_I]
  simp
  ring

theorem angularLogDifference_intervalIntegrable (theta : ℝ) :
    IntervalIntegrable (angularLogDifference theta) volume 0 Real.pi := by
  have hp : IntervalIntegrable (fun s : ℝ => logAbsSin (theta + s))
      volume 0 Real.pi := by
    have h := (logAbsSin_intervalIntegrable theta
      (theta + Real.pi)).comp_add_right theta
    simpa only [sub_self, zero_add, add_comm theta,
      add_sub_cancel_right] using h
  have hm : IntervalIntegrable (fun s : ℝ => logAbsSin (theta - s))
      volume 0 Real.pi := by
    have h := (logAbsSin_intervalIntegrable theta
      (theta - Real.pi)).comp_sub_left theta
    simpa only [sub_self, sub_sub_cancel] using h
  exact hp.sub hm

theorem intervalIntegrable_angularLogDifference_mul_cos
    (theta : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        angularLogDifference theta s * Real.cos (2 * n * s))
      volume 0 Real.pi := by
  exact (angularLogDifference_intervalIntegrable theta).mul_continuousOn
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_const |>.mul continuous_id)).continuousOn)

theorem intervalIntegrable_angularLogDifference_mul_sin
    (theta : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        angularLogDifference theta s * Real.sin (2 * n * s))
      volume 0 Real.pi := by
  exact (angularLogDifference_intervalIntegrable theta).mul_continuousOn
    ((Real.continuous_sin.comp
      (continuous_const.mul continuous_const |>.mul continuous_id)).continuousOn)

theorem fourierCoeffOn_angularLogDifferenceC_nat
    (theta : ℝ) (n : ℕ) (hn : 0 < n) :
    fourierCoeffOn Real.pi_pos (angularLogDifferenceC theta) (n : ℤ) =
      -Complex.I *
        ((Real.sin (2 * n * theta) / n : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hcosR := intervalIntegrable_angularLogDifference_mul_cos theta n
  have hsinR := intervalIntegrable_angularLogDifference_mul_sin theta n
  have hcosC : IntervalIntegrable
      (fun s : ℝ =>
        ((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ))
      volume 0 Real.pi := by
    exact ⟨hcosR.1.ofReal, hcosR.2.ofReal⟩
  have hsinC : IntervalIntegrable
      (fun s : ℝ =>
        ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ))
      volume 0 Real.pi := by
    exact ⟨hsinR.1.ofReal, hsinR.2.ofReal⟩
  have hintegrand : ∀ s : ℝ,
      fourier (-(n : ℤ)) (s : AddCircle (Real.pi - 0)) •
          angularLogDifferenceC theta s =
        ((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ) -
          Complex.I *
            ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ) := by
    intro s
    rw [fourier_neg_nat_on_pi_sub_zero]
    simp only [angularLogDifferenceC, smul_eq_mul]
    push_cast
    ring
  have hintegral :
      (∫ s : ℝ in 0..Real.pi,
        fourier (-(n : ℤ)) (s : AddCircle (Real.pi - 0)) •
          angularLogDifferenceC theta s) =
      ∫ s : ℝ in 0..Real.pi,
        (((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ) -
          Complex.I *
            ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact hintegrand s
  calc
    (1 / (Real.pi - 0)) •
        (∫ s : ℝ in 0..Real.pi,
          fourier (-(n : ℤ)) (s : AddCircle (Real.pi - 0)) •
            angularLogDifferenceC theta s) =
        (1 / (Real.pi - 0)) •
          (∫ s : ℝ in 0..Real.pi,
            (((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ) -
              Complex.I *
                ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ))) :=
      congrArg (fun z : ℂ => (1 / (Real.pi - 0)) • z) hintegral
    _ = -Complex.I *
        ((Real.sin (2 * n * theta) / n : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_sub hcosC (hsinC.const_mul Complex.I),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal,
        intervalIntegral.integral_ofReal,
        integral_angularLogDifference_mul_cos,
        integral_angularLogDifference_mul_sin theta n hn]
      rw [Complex.real_smul]
      push_cast
      field_simp [Real.pi_ne_zero, Nat.ne_of_gt hn]
      ring

theorem fourierCoeffOn_angularLogDifferenceC_neg_nat
    (theta : ℝ) (n : ℕ) (hn : 0 < n) :
    fourierCoeffOn Real.pi_pos (angularLogDifferenceC theta) (-(n : ℤ)) =
      Complex.I *
        ((Real.sin (2 * n * theta) / n : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hcosR := intervalIntegrable_angularLogDifference_mul_cos theta n
  have hsinR := intervalIntegrable_angularLogDifference_mul_sin theta n
  have hcosC : IntervalIntegrable
      (fun s : ℝ =>
        ((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ))
      volume 0 Real.pi := by
    exact ⟨hcosR.1.ofReal, hcosR.2.ofReal⟩
  have hsinC : IntervalIntegrable
      (fun s : ℝ =>
        ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ))
      volume 0 Real.pi := by
    exact ⟨hsinR.1.ofReal, hsinR.2.ofReal⟩
  have hintegrand : ∀ s : ℝ,
      fourier (-(-(n : ℤ))) (s : AddCircle (Real.pi - 0)) •
          angularLogDifferenceC theta s =
        ((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ) +
          Complex.I *
            ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ) := by
    intro s
    rw [neg_neg, fourier_pos_nat_on_pi_sub_zero]
    simp only [angularLogDifferenceC, smul_eq_mul]
    push_cast
    ring
  have hintegral :
      (∫ s : ℝ in 0..Real.pi,
        fourier (-(-(n : ℤ))) (s : AddCircle (Real.pi - 0)) •
          angularLogDifferenceC theta s) =
      ∫ s : ℝ in 0..Real.pi,
        (((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ) +
          Complex.I *
            ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact hintegrand s
  calc
    (1 / (Real.pi - 0)) •
        (∫ s : ℝ in 0..Real.pi,
          fourier (-(-(n : ℤ))) (s : AddCircle (Real.pi - 0)) •
            angularLogDifferenceC theta s) =
        (1 / (Real.pi - 0)) •
          (∫ s : ℝ in 0..Real.pi,
            (((angularLogDifference theta s * Real.cos (2 * n * s) : ℝ) : ℂ) +
              Complex.I *
                ((angularLogDifference theta s * Real.sin (2 * n * s) : ℝ) : ℂ))) :=
      congrArg (fun z : ℂ => (1 / (Real.pi - 0)) • z) hintegral
    _ = Complex.I *
        ((Real.sin (2 * n * theta) / n : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_add hcosC (hsinC.const_mul Complex.I),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal,
        intervalIntegral.integral_ofReal,
        integral_angularLogDifference_mul_cos,
        integral_angularLogDifference_mul_sin theta n hn]
      rw [Complex.real_smul]
      push_cast
      field_simp [Real.pi_ne_zero, Nat.ne_of_gt hn]
      ring

theorem fourierCoeffOn_angularLogDifferenceC_zero (theta : ℝ) :
    fourierCoeffOn Real.pi_pos (angularLogDifferenceC theta) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero]
  have hintegral :
      (∫ s : ℝ in 0..Real.pi,
        fourier (0 : ℤ) (s : AddCircle (Real.pi - 0)) •
          angularLogDifferenceC theta s) = 0 := by
    have hreal :
        (∫ s : ℝ in 0..Real.pi, angularLogDifference theta s) = 0 := by
      simpa using integral_angularLogDifference_mul_cos theta 0
    simp only [fourier_zero, one_smul, angularLogDifferenceC,
      intervalIntegral.integral_ofReal, hreal, Complex.ofReal_zero]
  rw [hintegral, smul_zero]

end HBL
