import HBL.AngularGreenSeries
import HBL.AngularLogDifferenceL2

/-!
The exact product integral for the angular logarithmic kernel.

This is the Parseval step which turns the rigorously computed Fourier
coefficients into the Dirichlet Green kernel on `(0, π / 2)`.
-/

noncomputable section

open Set MeasureTheory Complex
open scoped Interval ComplexConjugate

namespace HBL

theorem re_angularLogDifference_fourierCoeff_pair
    (theta phi : ℝ) (n : ℕ) :
    Complex.re
        (conj
            (fourierCoeffOn Real.pi_pos
              (angularLogDifferenceC theta) (n : ℤ)) *
            fourierCoeffOn Real.pi_pos
              (angularLogDifferenceC phi) (n : ℤ) +
          conj
            (fourierCoeffOn Real.pi_pos
              (angularLogDifferenceC theta) (-(n : ℤ))) *
            fourierCoeffOn Real.pi_pos
              (angularLogDifferenceC phi) (-(n : ℤ))) =
      2 * (1 / (n : ℝ) ^ 2 *
        (Real.sin (2 * n * theta) * Real.sin (2 * n * phi))) := by
  by_cases hn : n = 0
  · subst n
    simp [fourierCoeffOn_angularLogDifferenceC_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [fourierCoeffOn_angularLogDifferenceC_nat theta n hnpos,
      fourierCoeffOn_angularLogDifferenceC_nat phi n hnpos,
      fourierCoeffOn_angularLogDifferenceC_neg_nat theta n hnpos,
      fourierCoeffOn_angularLogDifferenceC_neg_nat phi n hnpos]
    simp only [map_mul, map_neg, conj_I, conj_ofReal, neg_mul,
      mul_neg, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    rw [Complex.I_sq]
    simp only [neg_mul, neg_neg, one_mul, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, zero_mul, sub_zero]
    field_simp [hn]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num
    field_simp [hn]

theorem integral_angularLogDifference_product_full
    {theta phi : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hphi : phi ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ s : ℝ in 0..Real.pi,
        angularLogDifference theta s * angularLogDifference phi s) =
      4 * Real.pi * min theta phi *
        (Real.pi / 2 - max theta phi) := by
  let q : ℤ → ℂ := fun i =>
    conj
        (fourierCoeffOn Real.pi_pos
          (angularLogDifferenceC theta) i) *
      fourierCoeffOn Real.pi_pos
        (angularLogDifferenceC phi) i
  let J : ℂ := ∫ s : ℝ in 0..Real.pi,
    conj (angularLogDifferenceC theta s) *
      angularLogDifferenceC phi s
  have hparseval : HasSum q ((Real.pi - 0)⁻¹ • J) := by
    exact hasSum_prod_fourierCoeffOn Real.pi_pos
      (memLp_angularLogDifferenceC_Ioc theta)
      (memLp_angularLogDifferenceC_Ioc phi)
  have hpairedC := hparseval.nat_add_neg
  have hpairedR := Complex.reCLM.hasSum hpairedC
  have hpairedR' :
      HasSum
        (fun n : ℕ =>
          2 * (1 / (n : ℝ) ^ 2 *
            (Real.sin (2 * n * theta) * Real.sin (2 * n * phi))))
        (Complex.re (((Real.pi - 0)⁻¹ • J) + q 0)) := by
    change HasSum
      (fun n : ℕ => Complex.re (q (n : ℤ) + q (-(n : ℤ))))
      (Complex.re (((Real.pi - 0)⁻¹ • J) + q 0)) at hpairedR
    refine hpairedR.congr_fun ?_
    intro n
    exact (re_angularLogDifference_fourierCoeff_pair theta phi n).symm
  have hseries :=
    (hasSum_sin_product_div_nat_sq htheta hphi).mul_left (2 : ℝ)
  have hvalue :
      Complex.re (((Real.pi - 0)⁻¹ • J) + q 0) =
        2 * (2 * min theta phi *
          (Real.pi / 2 - max theta phi)) :=
    hpairedR'.unique hseries
  have hJ : J =
      ((∫ s : ℝ in 0..Real.pi,
          angularLogDifference theta s * angularLogDifference phi s : ℝ) : ℂ) := by
    dsimp only [J]
    calc
      (∫ s : ℝ in 0..Real.pi,
          conj (angularLogDifferenceC theta s) *
            angularLogDifferenceC phi s) =
          ∫ s : ℝ in 0..Real.pi,
            ((angularLogDifference theta s *
              angularLogDifference phi s : ℝ) : ℂ) := by
            apply intervalIntegral.integral_congr
            intro s _
            simp only [angularLogDifferenceC, conj_ofReal, ofReal_mul]
      _ = ((∫ s : ℝ in 0..Real.pi,
          angularLogDifference theta s *
            angularLogDifference phi s : ℝ) : ℂ) :=
        intervalIntegral.integral_ofReal
  dsimp only [q] at hvalue
  rw [fourierCoeffOn_angularLogDifferenceC_zero theta,
    fourierCoeffOn_angularLogDifferenceC_zero phi] at hvalue
  simp only [map_zero, zero_mul, add_zero] at hvalue
  rw [hJ] at hvalue
  simp only [sub_zero, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hvalue
  field_simp [Real.pi_ne_zero] at hvalue
  nlinarith [Real.pi_pos]

theorem integral_angularLogDifference_product_half
    {theta phi : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hphi : phi ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ s : ℝ in 0..Real.pi / 2,
        angularLogDifference theta s * angularLogDifference phi s) =
      2 * Real.pi * min theta phi *
        (Real.pi / 2 - max theta phi) := by
  let p : ℝ → ℝ := fun s =>
    angularLogDifference theta s * angularLogDifference phi s
  have hpMem : MemLp p 1 (volume.restrict (Ioc 0 Real.pi)) := by
    change MemLp
      ((angularLogDifference theta) * (angularLogDifference phi)) 1
      (volume.restrict (Ioc 0 Real.pi))
    exact MeasureTheory.MemLp.mul
      (memLp_angularLogDifference_Ioc theta)
      (memLp_angularLogDifference_Ioc phi)
  have hpInt : IntervalIntegrable p volume 0 Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    exact memLp_one_iff_integrable.mp hpMem
  have hmid : Real.pi / 2 ∈ uIcc (0 : ℝ) Real.pi := by
    rw [uIcc_of_le Real.pi_pos.le]
    constructor <;> nlinarith [Real.pi_pos]
  have hpLeft : IntervalIntegrable p volume 0 (Real.pi / 2) :=
    hpInt.mono_set (uIcc_subset_uIcc_left hmid)
  have hpRight : IntervalIntegrable p volume (Real.pi / 2) Real.pi :=
    hpInt.mono_set (uIcc_subset_uIcc_right hmid)
  have hpReflect (s : ℝ) : p (Real.pi - s) = p s := by
    simp only [p, angularLogDifference_reflect]
    ring
  have hleftReflect :
      (∫ s : ℝ in 0..Real.pi / 2, p (Real.pi - s)) =
        ∫ s : ℝ in 0..Real.pi / 2, p s := by
    apply intervalIntegral.integral_congr
    intro s _
    exact hpReflect s
  have hsubstitution := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := Real.pi / 2) p Real.pi
  have hendpoint : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
  rw [hendpoint] at hsubstitution
  have hrightEqualsLeft :
      (∫ s : ℝ in Real.pi / 2..Real.pi, p s) =
        ∫ s : ℝ in 0..Real.pi / 2, p s :=
    by simpa only [sub_zero] using hsubstitution.symm.trans hleftReflect
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hpLeft hpRight
  rw [hrightEqualsLeft] at hsplit
  have hfull := integral_angularLogDifference_product_full htheta hphi
  change (∫ s : ℝ in 0..Real.pi / 2, p s) = _
  change (∫ s : ℝ in 0..Real.pi, p s) = _ at hfull
  rw [hfull] at hsplit
  nlinarith

end HBL
