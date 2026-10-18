import Mathlib.NumberTheory.ZetaValues

/-!
The scalar sine-series identity behind the angular Green kernel.

The series is indexed by all natural numbers; its zero term vanishes.  This
convention matches the Fourier-series results already available in Mathlib.
-/

noncomputable section

open Set

namespace HBL

set_option maxHeartbeats 800000 in
theorem hasSum_cos_two_pi_div_nat_sq
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum
      (fun n : ℕ =>
        1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x))
      (Real.pi ^ 2 * (x ^ 2 - x + 6⁻¹)) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  change HasSum
      (fun n : ℕ =>
        1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * x))
      ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / Nat.factorial 2 *
        bernoulliFun 2 x) at h
  rw [bernoulliFun_two] at h
  have hcoefficient :
      ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 /
          (Nat.factorial 2 : ℝ)) = Real.pi ^ 2 := by
    norm_num [Nat.factorial]
    ring
  have heq :
      ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 /
          (Nat.factorial 2 : ℝ) * (x ^ 2 - x + 6⁻¹)) =
        Real.pi ^ 2 * (x ^ 2 - x + 6⁻¹) := by
    rw [hcoefficient]
  rw [heq] at h
  exact h

set_option maxHeartbeats 800000 in
theorem hasSum_sin_product_div_nat_sq_of_le
    {theta phi : ℝ}
    (htheta0 : 0 ≤ theta) (hθφ : theta ≤ phi)
    (hphi : phi ≤ Real.pi / 2) :
    HasSum
      (fun n : ℕ =>
        1 / (n : ℝ) ^ 2 *
          (Real.sin (2 * n * theta) * Real.sin (2 * n * phi)))
      (2 * theta * (Real.pi / 2 - phi)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff0 : 0 ≤ (phi - theta) / Real.pi :=
    div_nonneg (sub_nonneg.mpr hθφ) hpi.le
  have hdiff1 : (phi - theta) / Real.pi ≤ 1 := by
    apply (div_le_one hpi).2
    linarith
  have hplus0 : 0 ≤ (theta + phi) / Real.pi := by
    apply div_nonneg
    · linarith
    · exact hpi.le
  have hplus1 : (theta + phi) / Real.pi ≤ 1 := by
    apply (div_le_one hpi).2
    linarith
  have hd := hasSum_cos_two_pi_div_nat_sq
    (x := (phi - theta) / Real.pi) ⟨hdiff0, hdiff1⟩
  have hp := hasSum_cos_two_pi_div_nat_sq
    (x := (theta + phi) / Real.pi) ⟨hplus0, hplus1⟩
  have h := (hd.sub hp).div_const (2 : ℝ)
  have hterm : ∀ n : ℕ,
      1 / (n : ℝ) ^ 2 *
          (Real.sin (2 * n * theta) * Real.sin (2 * n * phi)) =
        ((1 / (n : ℝ) ^ 2 *
            Real.cos (2 * Real.pi * n * ((phi - theta) / Real.pi)) -
          1 / (n : ℝ) ^ 2 *
            Real.cos (2 * Real.pi * n * ((theta + phi) / Real.pi))) / 2) := by
    intro n
    have hdiffarg :
        2 * Real.pi * (n : ℝ) * ((phi - theta) / Real.pi) =
          -(2 * (n : ℝ) * theta - 2 * (n : ℝ) * phi) := by
      field_simp [Real.pi_ne_zero]
      ring
    have hplusarg :
        2 * Real.pi * (n : ℝ) * ((theta + phi) / Real.pi) =
          2 * (n : ℝ) * theta + 2 * (n : ℝ) * phi := by
      field_simp [Real.pi_ne_zero]
    rw [hdiffarg, hplusarg, Real.cos_neg]
    calc
      1 / (n : ℝ) ^ 2 *
            (Real.sin (2 * n * theta) * Real.sin (2 * n * phi)) =
          (1 / (n : ℝ) ^ 2 *
            (2 * Real.sin (2 * n * theta) * Real.sin (2 * n * phi))) / 2 := by
              ring
      _ = (1 / (n : ℝ) ^ 2 *
            (Real.cos (2 * n * theta - 2 * n * phi) -
              Real.cos (2 * n * theta + 2 * n * phi))) / 2 := by
              rw [Real.two_mul_sin_mul_sin]
      _ = (1 / (n : ℝ) ^ 2 *
              Real.cos (2 * n * theta - 2 * n * phi) -
            1 / (n : ℝ) ^ 2 *
              Real.cos (2 * n * theta + 2 * n * phi)) / 2 := by
              ring
  have hvalue :
      (Real.pi ^ 2 *
            (((phi - theta) / Real.pi) ^ 2 -
              (phi - theta) / Real.pi + 6⁻¹) -
          Real.pi ^ 2 *
            (((theta + phi) / Real.pi) ^ 2 -
              (theta + phi) / Real.pi + 6⁻¹)) / 2 =
        2 * theta * (Real.pi / 2 - phi) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hvalue] at h
  exact h.congr_fun hterm

set_option maxHeartbeats 800000 in
theorem hasSum_sin_product_div_nat_sq
    {theta phi : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hphi : phi ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    HasSum
      (fun n : ℕ =>
        1 / (n : ℝ) ^ 2 *
          (Real.sin (2 * n * theta) * Real.sin (2 * n * phi)))
      (2 * min theta phi * (Real.pi / 2 - max theta phi)) := by
  rcases le_total theta phi with hθφ | hφθ
  · simpa [min_eq_left hθφ, max_eq_right hθφ] using
      hasSum_sin_product_div_nat_sq_of_le htheta.1 hθφ hphi.2
  · have h := hasSum_sin_product_div_nat_sq_of_le
      hphi.1 hφθ htheta.2
    simpa [min_eq_right hφθ, max_eq_left hφθ, mul_comm] using h

theorem tsum_sin_product_div_nat_sq
    {theta phi : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hphi : phi ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (∑' n : ℕ,
        1 / (n : ℝ) ^ 2 *
          (Real.sin (2 * n * theta) * Real.sin (2 * n * phi))) =
      2 * min theta phi * (Real.pi / 2 - max theta phi) :=
  (hasSum_sin_product_div_nat_sq htheta hphi).tsum_eq

end HBL
