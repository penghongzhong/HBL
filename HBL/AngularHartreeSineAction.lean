import HBL.AngularHartreeComposition

/-!
The positive sine action of the actual angular logarithmic Hartree kernel.
Reflection halves the already proved full-period integral because both the
logarithmic difference and the sine change sign. No new Fourier expansion,
odd-sector replacement kernel, or spectral hypothesis is introduced.
-/

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace HBL.Modulation.Monopole

private theorem angularLogDifference_sine_half (theta : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫ s : ℝ in 0..Real.pi / 2,
      HBL.angularLogDifference theta s * Real.sin (2 * n * s)) =
        Real.pi / (2 * n) * Real.sin (2 * n * theta) := by
  let p : ℝ → ℝ := fun s =>
    HBL.angularLogDifference theta s * Real.sin (2 * n * s)
  have hpInt : IntervalIntegrable p volume 0 Real.pi :=
    HBL.intervalIntegrable_angularLogDifference_mul_sin theta n
  have hmid : Real.pi / 2 ∈ uIcc (0 : ℝ) Real.pi := by
    rw [uIcc_of_le Real.pi_pos.le]
    constructor <;> nlinarith [Real.pi_pos]
  have hleft := hpInt.mono_set (uIcc_subset_uIcc_left hmid)
  have hright := hpInt.mono_set (uIcc_subset_uIcc_right hmid)
  have hreflect (s : ℝ) : p (Real.pi - s) = p s := by
    have hsin : Real.sin (2 * (n : ℝ) * (Real.pi - s)) =
        -Real.sin (2 * n * s) := by
      rw [show 2 * (n : ℝ) * (Real.pi - s) =
        n * (2 * Real.pi) - 2 * n * s by ring]
      exact Real.sin_nat_mul_two_pi_sub (2 * n * s) n
    simp only [p, HBL.angularLogDifference_reflect, hsin, neg_mul_neg]
  have hleftReflect :
      (∫ s : ℝ in 0..Real.pi / 2, p (Real.pi - s)) =
        ∫ s : ℝ in 0..Real.pi / 2, p s := by
    apply intervalIntegral.integral_congr
    intro s _
    exact hreflect s
  have hsubstitution := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := Real.pi / 2) p Real.pi
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at hsubstitution
  have hequal : (∫ s : ℝ in Real.pi / 2..Real.pi, p s) =
      ∫ s : ℝ in 0..Real.pi / 2, p s := by
    simpa only [sub_zero] using hsubstitution.symm.trans hleftReflect
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [hequal] at hsplit
  have hfull := HBL.integral_angularLogDifference_mul_sin theta n hn
  change (∫ s : ℝ in 0..Real.pi, p s) = _ at hfull
  rw [hfull] at hsplit
  change (∫ s : ℝ in 0..Real.pi / 2, p s) = _
  have hcoefficient : Real.pi / (n : ℝ) = 2 * (Real.pi / (2 * n)) := by ring
  rw [hcoefficient] at hsplit
  linarith

private theorem angularHartreeLog_sine_ae {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    (fun s => HBL.angularLogDifference theta s * Real.sin (2 * n * s))
      =ᵐ[volume.restrict (uIoc (0 : ℝ) (Real.pi / 2))]
        (fun s => angularHartreeLog theta s * Real.sin (2 * n * s)) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    (Measure.ae_ne volume theta).filter_mono ae_restrict_le,
    (Measure.ae_ne volume (Real.pi / 2)).filter_mono ae_restrict_le]
      with s hs hsTheta hsEnd
  rw [uIoc_of_le (by positivity)] at hs
  rw [angularLogDifference_eq_angularHartreeLog htheta hs.1
    (lt_of_le_of_ne hs.2 hsEnd) hsTheta.symm]

/-- The actual singular angular kernel times a sine is absolutely integrable
on the half interval. The diagonal and the upper endpoint are null sets. -/
theorem angularHartreeLog_sine_intervalIntegrable {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    IntervalIntegrable
      (fun s => angularHartreeLog theta s * Real.sin (2 * n * s))
      volume 0 (Real.pi / 2) := by
  have hmid : Real.pi / 2 ∈ uIcc (0 : ℝ) Real.pi := by
    rw [uIcc_of_le Real.pi_pos.le]
    constructor <;> nlinarith [Real.pi_pos]
  exact ((HBL.intervalIntegrable_angularLogDifference_mul_sin theta n).mono_set
    (uIcc_subset_uIcc_left hmid)).congr_ae (angularHartreeLog_sine_ae htheta n)

/-- Positive, sign-resolved sine action of the actual half-interval kernel. -/
theorem integral_angularHartreeLog_mul_sin_half {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) (n : ℕ) (hn : 0 < n) :
    (∫ s : ℝ in 0..Real.pi / 2,
      angularHartreeLog theta s * Real.sin (2 * n * s)) =
        Real.pi / (2 * n) * Real.sin (2 * n * theta) := by
  calc
    _ = ∫ s : ℝ in 0..Real.pi / 2,
        HBL.angularLogDifference theta s * Real.sin (2 * n * s) :=
      intervalIntegral.integral_congr_ae_restrict (angularHartreeLog_sine_ae htheta n).symm
    _ = _ := angularLogDifference_sine_half theta n hn

/-- With the actual Hartree normalization `24 / pi`, the sine multiplier
is `12 / n`, with its positive sign proved directly from the kernel integral. -/
theorem integral_normalizedAngularHartreeLog_mul_sin {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) (n : ℕ) (hn : 0 < n) :
    (∫ s : ℝ in 0..Real.pi / 2,
      (24 / Real.pi) * angularHartreeLog theta s * Real.sin (2 * n * s)) =
        (12 / n) * Real.sin (2 * n * theta) := by
  calc
    _ = (24 / Real.pi) * ∫ s : ℝ in 0..Real.pi / 2,
        angularHartreeLog theta s * Real.sin (2 * n * s) := by
      simp only [mul_assoc, intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [integral_angularHartreeLog_mul_sin_half htheta n hn]
      field_simp [Real.pi_ne_zero]
      ring

end HBL.Modulation.Monopole
