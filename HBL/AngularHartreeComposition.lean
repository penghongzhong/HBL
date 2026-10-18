import HBL.AngularLogDifferenceProduct
import HBL.WeightedArctanKernels
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
Identification of the periodic logarithmic representative with the angular
Hartree kernel, followed by the arctangent change of variables on the radial
half-line.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace HBL.Modulation.Monopole

theorem angularLogDifference_eq_angularHartreeLog
    {theta s : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hs0 : 0 < s) (hshalf : s < Real.pi / 2)
    (hne : theta ≠ s) :
    HBL.angularLogDifference theta s = angularHartreeLog theta s := by
  have hsum0 : 0 < theta + s := by linarith [htheta.1]
  have hsumpi : theta + s < Real.pi := by
    nlinarith [htheta.2, hshalf, Real.pi_pos]
  have hsumSin : 0 < Real.sin (theta + s) :=
    Real.sin_pos_of_pos_of_lt_pi hsum0 hsumpi
  have hdiffLow : -Real.pi < theta - s := by
    nlinarith [htheta.1, hshalf, Real.pi_pos]
  have hdiffHigh : theta - s < Real.pi := by
    nlinarith [htheta.2, hs0, Real.pi_pos]
  have hdiffSin : Real.sin (theta - s) ≠ 0 := by
    intro hzero
    have hdiffZero :=
      (Real.sin_eq_zero_iff_of_lt_of_lt hdiffLow hdiffHigh).mp hzero
    exact hne (sub_eq_zero.mp hdiffZero)
  unfold HBL.angularLogDifference HBL.logAbsSin angularHartreeLog
  rw [abs_of_pos hsumSin,
    Real.log_div hsumSin.ne' (abs_ne_zero.mpr hdiffSin)]

theorem integral_angularHartreeLog_product
    {theta phi : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hphi : phi ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ s : ℝ in 0..Real.pi / 2,
        angularHartreeLog theta s * angularHartreeLog phi s) =
      2 * Real.pi * min theta phi *
        (Real.pi / 2 - max theta phi) := by
  calc
    (∫ s : ℝ in 0..Real.pi / 2,
        angularHartreeLog theta s * angularHartreeLog phi s) =
        ∫ s : ℝ in 0..Real.pi / 2,
          HBL.angularLogDifference theta s *
            HBL.angularLogDifference phi s := by
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        (Measure.ae_ne volume theta).filter_mono ae_restrict_le,
        (Measure.ae_ne volume phi).filter_mono ae_restrict_le,
        (Measure.ae_ne volume (Real.pi / 2)).filter_mono ae_restrict_le]
          with s hs hsTheta hsPhi hsEnd
      rw [uIoc_of_le (by positivity)] at hs
      have hsHalf : s < Real.pi / 2 := lt_of_le_of_ne hs.2 hsEnd
      rw [← angularLogDifference_eq_angularHartreeLog htheta hs.1 hsHalf
          hsTheta.symm,
        ← angularLogDifference_eq_angularHartreeLog hphi hs.1 hsHalf
          hsPhi.symm]
    _ = 2 * Real.pi * min theta phi *
        (Real.pi / 2 - max theta phi) :=
      HBL.integral_angularLogDifference_product_half htheta hphi

theorem arctan_image_Ioi :
    Real.arctan '' Ioi (0 : ℝ) = Ioo 0 (Real.pi / 2) := by
  ext theta
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨Real.arctan_pos.mpr hr, Real.arctan_lt_pi_div_two r⟩
  · intro htheta
    refine ⟨Real.tan theta,
      Real.tan_pos_of_pos_of_lt_pi_div_two htheta.1 htheta.2, ?_⟩
    exact Real.arctan_tan (by nlinarith [htheta.1, Real.pi_pos]) htheta.2

theorem bubble_sq (r : ℝ) :
    bubble r ^ 2 = (1 + r ^ 2)⁻¹ := by
  unfold bubble
  rw [inv_pow, Real.sq_sqrt (by positivity)]

theorem integral_Ioo_eq_integral_Ioi_arctan (g : ℝ → ℝ) :
    (∫ theta in Ioo 0 (Real.pi / 2), g theta) =
      ∫ r in Ioi 0, bubble r ^ 2 * g (Real.arctan r) := by
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Ioi (0 : ℝ)) (f := Real.arctan)
      (f' := fun r : ℝ => (1 + r ^ 2)⁻¹)
      measurableSet_Ioi
      (fun r _ => (Real.hasDerivAt_arctan' r).hasDerivWithinAt)
      Real.arctan_injective.injOn g
  rw [arctan_image_Ioi] at hchange
  calc
    (∫ theta in Ioo 0 (Real.pi / 2), g theta) =
        ∫ r in Ioi 0,
          |(1 + r ^ 2)⁻¹| • g (Real.arctan r) := hchange
    _ = ∫ r in Ioi 0, bubble r ^ 2 * g (Real.arctan r) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      change |(1 + r ^ 2)⁻¹| * g (Real.arctan r) =
        bubble r ^ 2 * g (Real.arctan r)
      rw [abs_of_pos (by positivity : 0 < (1 + r ^ 2)⁻¹),
        bubble_sq]

theorem intervalIntegral_eq_integral_Ioi_arctan (g : ℝ → ℝ) :
    (∫ theta : ℝ in 0..Real.pi / 2, g theta) =
      ∫ r in Ioi 0, bubble r ^ 2 * g (Real.arctan r) := by
  rw [intervalIntegral.integral_of_le (by positivity)]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact integral_Ioo_eq_integral_Ioi_arctan g

theorem angularHartreeLog_symm (theta phi : ℝ) :
    angularHartreeLog theta phi = angularHartreeLog phi theta := by
  unfold angularHartreeLog
  rw [add_comm theta phi]
  have hdiff : |Real.sin (theta - phi)| =
      |Real.sin (phi - theta)| := by
    rw [show phi - theta = -(theta - phi) by ring,
      Real.sin_neg, abs_neg]
  rw [hdiff]

/-- Dirichlet Green kernel of `-∂²` on the angular interval. -/
def angularZeroGreen (theta phi : ℝ) : ℝ :=
  (2 / Real.pi) * min theta phi *
    (Real.pi / 2 - max theta phi)

/-- Pullback of the angular zero-energy Green kernel to the radial half-line. -/
def weightedZeroGreen (r rho : ℝ) : ℝ :=
  bubble r * bubble rho *
    angularZeroGreen (Real.arctan r) (Real.arctan rho)

theorem weightedHartreeKernel_square_integral
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    (∫ s in Ioi (0 : ℝ),
        weightedHartreeKernel r s * weightedHartreeKernel s rho) =
      576 * weightedZeroGreen r rho := by
  have htheta : Real.arctan r ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(Real.arctan_pos.mpr hr).le, (Real.arctan_lt_pi_div_two r).le⟩
  have hphi : Real.arctan rho ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨(Real.arctan_pos.mpr hrho).le,
      (Real.arctan_lt_pi_div_two rho).le⟩
  let c : ℝ := (576 / Real.pi ^ 2) * bubble r * bubble rho
  let g : ℝ → ℝ := fun sigma =>
    angularHartreeLog (Real.arctan r) sigma *
      angularHartreeLog (Real.arctan rho) sigma
  calc
    (∫ s in Ioi (0 : ℝ),
        weightedHartreeKernel r s * weightedHartreeKernel s rho) =
        ∫ s in Ioi (0 : ℝ), c * (bubble s ^ 2 * g (Real.arctan s)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi,
        (Measure.ae_ne volume r).filter_mono ae_restrict_le,
        (Measure.ae_ne volume rho).filter_mono ae_restrict_le]
          with s hs hsr hsrho
      rw [weightedHartreeKernel_eq_angular r s hsr.symm,
        weightedHartreeKernel_eq_angular s rho hsrho,
        angularHartreeLog_symm (Real.arctan s) (Real.arctan rho)]
      dsimp only [c, g]
      ring
    _ = c * ∫ s in Ioi (0 : ℝ), bubble s ^ 2 * g (Real.arctan s) := by
      rw [MeasureTheory.integral_const_mul]
    _ = c * ∫ sigma : ℝ in 0..Real.pi / 2, g sigma := by
      rw [intervalIntegral_eq_integral_Ioi_arctan]
    _ = 576 * weightedZeroGreen r rho := by
      rw [show (∫ sigma : ℝ in 0..Real.pi / 2, g sigma) =
          2 * Real.pi * min (Real.arctan r) (Real.arctan rho) *
            (Real.pi / 2 - max (Real.arctan r) (Real.arctan rho)) by
        exact integral_angularHartreeLog_product htheta hphi]
      dsimp only [c, g, weightedZeroGreen, angularZeroGreen]
      field_simp [Real.pi_ne_zero]

end HBL.Modulation.Monopole
